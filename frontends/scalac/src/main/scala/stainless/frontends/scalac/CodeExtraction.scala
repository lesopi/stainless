/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package frontends.scalac

import stainless.ast.SymbolIdentifier
import extraction.xlang.{trees => xt}

import scala.reflect.internal.util._
import scala.collection.mutable.{Map => MutableMap, ListBuffer}

import scala.language.implicitConversions

trait CodeExtraction extends ASTExtractors {
  self: StainlessExtraction =>

  import global._
  import global.definitions._
  import StructuralExtractors._
  import ExpressionExtractors._
  import scala.collection.immutable.Set

  lazy val reporter = self.ctx.reporter

  implicit def scalaPosToInoxPos(p: global.Position): inox.utils.Position = {
    if (p == NoPosition) {
      inox.utils.NoPosition
    } else if (p.isRange) {
      val start = p.focusStart
      val end   = p.focusEnd
      inox.utils.RangePosition(start.line, start.column, start.point,
                               end.line, end.column, end.point,
                               p.source.file.file)
    } else {
      inox.utils.OffsetPosition(p.line, p.column, p.point,
                                p.source.file.file)
    }
  }

  /** An exception thrown when non-purescala compatible code is encountered. */
  sealed class ImpureCodeEncounteredException(val pos: Position, msg: String, val ot: Option[Tree])
    extends Exception(msg)

  def outOfSubsetError(pos: Position, msg: String) = {
    throw new ImpureCodeEncounteredException(pos, msg, None)
  }

  def outOfSubsetError(t: Tree, msg: String) = {
    throw new ImpureCodeEncounteredException(t.pos, msg, Some(t))
  }

  class Extraction(compilationUnits: List[CompilationUnit]) {

    private val symbolToSymbol: MutableMap[Symbol, ast.Symbol] = MutableMap.empty
    private val symbolToIdentifier: MutableMap[Symbol, SymbolIdentifier] = MutableMap.empty
    private def getIdentifier(sym: Symbol): SymbolIdentifier = {
      //val sym = s.accessedOrSelf.orElse(s)
      symbolToIdentifier.get(sym) match {
        case Some(id) => id
        case None =>
          val top = if (sym.overrideChain.nonEmpty) sym.overrideChain.last else sym
          val symbol = symbolToSymbol.get(top) match {
            case Some(symbol) => symbol
            case None =>
              val name = sym.fullName.toString.trim
              val symbol = ast.Symbol(if (name.endsWith("$")) name.init else name)
              symbolToSymbol += top -> symbol
              symbol
          }

          val id = SymbolIdentifier(symbol)
          symbolToIdentifier += sym -> id
          id
      }
    }

    private val symbolToTypeParams: MutableMap[Symbol, Seq[xt.TypeParameter]] = MutableMap.empty
    private def getTypeParams(sym: Symbol): Seq[xt.TypeParameter] = {
      val root: Symbol = {
        def rec(sym: Symbol): Symbol = sym.tpe.parents.headOption match {
          case Some(tpe) if ignoreClasses(tpe) => sym
          case Some(TypeRef(_, parentSym, tps)) => rec(parentSym)
          case _ => outOfSubsetError(sym.pos, "Unexpected parent type " + sym.tpe)
        }
        rec(sym)
      }

      symbolToTypeParams.get(root) match {
        case Some(tparams) => tparams
        case None =>
          val tparams = root.tpe match {
            case TypeRef(_, _, tps) => extractTypeParams(tps).map(sym => xt.TypeParameter.fresh(sym.name.toString))
            case _ => Nil
          }
          symbolToTypeParams += root -> tparams
          tparams
      }
    }

    private def annotationsOf(sym: Symbol, ignoreOwner: Boolean = false): Set[xt.Flag] = {
      val actualSymbol = sym.accessedOrSelf
      (for {
        a <- actualSymbol.annotations ++ (if (!ignoreOwner) actualSymbol.owner.annotations else Set.empty)
        name = a.atp.safeToString.replaceAll("\\.package\\.", ".")
      } yield {
        if (name startsWith "stainless.annotation.") {
          val shortName = name drop "stainless.annotation.".length
          Some(xt.extractFlag(shortName, a.args.map(extractTree(_)(DefContext()))))
        } else if (name == "inline") {
          Some(xt.extractFlag(name, a.args.map(extractTree(_)(DefContext()))))
        } else {
          None
        }
      }).flatten.toSet
    }

    case class DefContext(
      tparams: Map[Symbol, xt.TypeParameter] = Map(),
      vars: Map[Symbol, () => xt.Expr] = Map(),
      mutableVars: Map[Symbol, () => xt.Variable] = Map(),
      localFuns: Map[Symbol, (xt.ValDef, Seq[xt.TypeParameterDef])] = Map(),
      isExtern: Boolean = false
    ){
      def union(that: DefContext) = {
        copy(this.tparams ++ that.tparams,
             this.vars ++ that.vars,
             this.mutableVars ++ that.mutableVars,
             this.localFuns ++ that.localFuns,
             this.isExtern || that.isExtern)
      }

      def isVariable(s: Symbol) = (vars contains s) || (mutableVars contains s)

      def withNewVars(nvars: Traversable[(Symbol, () => xt.Expr)]) = {
        copy(vars = vars ++ nvars)
      }

      def withNewVar(s: Symbol, v: () => xt.Variable) = {
        copy(vars = vars + (s -> v))
      }

      def withNewMutableVar(s: Symbol, v: () => xt.Variable) = {
        copy(mutableVars = mutableVars + (s -> v))
      }

      def withNewMutableVars(nvars: Traversable[(Symbol, () => xt.Variable)]) = {
        copy(mutableVars = mutableVars ++ nvars)
      }

      def withLocalFun(sym: Symbol, vd: xt.ValDef, tparams: Seq[xt.TypeParameterDef]) = {
        copy(localFuns = this.localFuns + (sym -> ((vd, tparams))))
      }
    }

    def extractProgram: (List[xt.UnitDef], Program { val trees: xt.type }) = {
      val unitsAcc     = new ListBuffer[xt.UnitDef]
      val classesAcc   = new ListBuffer[xt.ClassDef]
      val functionsAcc = new ListBuffer[xt.FunDef]

      for (u <- compilationUnits) {
        val (id, stats) = u.body match {
          // package object
          case PackageDef(refTree, List(pd @ PackageDef(inner, body))) =>
            (FreshIdentifier(extractRef(inner).mkString("$")), pd.stats)

          case pd @ PackageDef(refTree, lst) =>
            (FreshIdentifier(u.source.file.name.replaceFirst("[.][^.]+$", "")), pd.stats)

          case _ => outOfSubsetError(u.body, "Unexpected unit body")
        }

        val (imports, classes, functions, subs, allClasses, allFunctions) = extractStatic(stats)
        assert(functions.isEmpty, "Packages shouldn't contain functions")

        unitsAcc += xt.UnitDef(
          id,
          imports,
          classes,
          subs,
          !(Main.libraryFiles contains u.source.file.absolute.path)
        ).setPos(u.body.pos)

        classesAcc ++= allClasses
        functionsAcc ++= allFunctions
      }

      val program: Program { val trees: xt.type } = new inox.Program {
        val trees: xt.type = xt
        val ctx = self.ctx
        val symbols = xt.NoSymbols.withClasses(classesAcc).withFunctions(functionsAcc)
      }

      (unitsAcc.toList, program)
    }

    // This one never fails, on error, it returns Untyped
    def stainlessType(tpt: Type)(implicit dctx: DefContext, pos: Position): xt.Type = {
      try {
        extractType(tpt)
      } catch {
        case e: ImpureCodeEncounteredException =>
          e.printStackTrace()
          xt.Untyped
      }
    }

    private def extractStatic(stats: List[Tree]): (
      Seq[xt.Import],
      Seq[Identifier],
      Seq[Identifier],
      Seq[xt.ModuleDef],
      Seq[xt.ClassDef],
      Seq[xt.FunDef]
    ) = {
      var imports   : Seq[xt.Import]    = Seq.empty
      var classes   : Seq[Identifier]   = Seq.empty
      var functions : Seq[Identifier]   = Seq.empty
      var subs      : Seq[xt.ModuleDef] = Seq.empty

      var allClasses   : Seq[xt.ClassDef] = Seq.empty
      var allFunctions : Seq[xt.FunDef]   = Seq.empty

      for (d <- stats) d match {
        case EmptyTree =>
          // ignore

        case t if (annotationsOf(t.symbol) contains xt.Ignore) || (t.symbol.isSynthetic) =>
          // ignore

        case ExtractorHelpers.ExSymbol("stainless", "annotation", "ignore") =>
          // ignore (can't be @ignored because of the dotty compiler)

        case ExConstructorDef() 
           | ExLazyFieldDef()
           | ExFieldAccessorFunction() =>
          // ignore

        case i @ Import(_, _) =>
          imports ++= extractImports(i)

        case td @ ExObjectDef(_, _) =>
          val (obj, newClasses, newFunctions) = extractObject(td)
          subs :+= obj
          allClasses ++= newClasses
          allFunctions ++= newFunctions

        case cd: ClassDef =>
          val (xcd, newFunctions) = extractClass(cd)
          classes :+= xcd.id
          allClasses :+= xcd
          allFunctions ++= newFunctions

        case dd @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
          val fd = extractFunction(fsym, tparams, vparams, rhs)(DefContext())
          functions :+= fd.id
          allFunctions :+= fd

        case t @ ExFieldDef(fsym, _, rhs) =>
          val fd = extractFunction(fsym, Seq.empty, Seq.empty, rhs)(DefContext())
          functions :+= fd.id
          allFunctions :+= fd

        case t @ ExLazyAccessorFunction(fsym, _, rhs) =>
          val fd = extractFunction(fsym, Seq.empty, Seq.empty, rhs)(DefContext())
          functions :+= fd.id
          allFunctions :+= fd

        case other =>
          reporter.warning(other.pos, "Could not extract tree in static container: " + other)
      }

      (imports, classes, functions, subs, allClasses, allFunctions)
    }

    def extractPackage(id: Identifier, u: CompilationUnit, pd: PackageDef): (xt.UnitDef, Seq[xt.ClassDef], Seq[xt.FunDef]) = {
      val (imports, classes, functions, subs, allClasses, allFunctions) = extractStatic(pd.stats)
      assert(functions.isEmpty, "Packages shouldn't contain functions")

      val unit = xt.UnitDef(
        id,
        imports,
        classes,
        subs,
        !(Main.libraryFiles contains u.source.file.absolute.path)
      ).setPos(pd.pos)

      (unit, allClasses, allFunctions)
    }

    private def extractObject(obj: ClassDef): (xt.ModuleDef, Seq[xt.ClassDef], Seq[xt.FunDef]) = {
      val ExObjectDef(_, template) = obj
      val (imports, classes, functions, subs, allClasses, allFunctions) = extractStatic(template.body)

      val module = xt.ModuleDef(
        getIdentifier(obj.symbol),
        imports,
        classes,
        functions,
        subs
      ).setPos(obj.pos)

      (module, allClasses, allFunctions)
    }

    private val ignoreClasses = Set(
      ObjectClass.tpe,
      SerializableClass.tpe,
      ProductRootClass.tpe,
      AnyRefClass.tpe
    )

    private val invSymbol = stainless.ast.Symbol("inv")

    private def extractClass(cd: ClassDef): (xt.ClassDef, Seq[xt.FunDef]) = {
      val sym = cd.symbol
      val id = getIdentifier(sym)

      val parent = sym.tpe.parents.headOption match {
        case Some(tpe) if ignoreClasses(tpe) => None
        case Some(TypeRef(_, parentSym, tps)) => Some(getIdentifier(parentSym))
        case _ => None
      }

      val tparams = getTypeParams(sym)

      val tparamsSyms = sym.tpe match {
        case TypeRef(_, _, tps) => extractTypeParams(tps)
        case _ => Nil
      }

      val tpCtx = DefContext((tparamsSyms zip tparams).toMap)

      val flags = annotationsOf(sym) ++ (if (sym.isAbstractClass) Some(xt.IsAbstract) else None)

      val constructor = cd.impl.children.find {
        case ExConstructorDef() => true
        case _ => false
      }.get.asInstanceOf[DefDef]

      val vds = constructor.vparamss.flatten
      val symbols = cd.impl.children.collect {
        case df @ DefDef(_, name, _, _, _, _)
        if df.symbol.isAccessor && df.symbol.isParamAccessor && !name.endsWith("_$eq") => df.symbol
      }

      val fields = (symbols zip vds).map { case (sym, vd) =>
        val tpe = stainlessType(vd.tpt.tpe)(tpCtx, vd.pos)
        val id = getIdentifier(sym)
        val flags = annotationsOf(sym, ignoreOwner = true)
        if (sym.accessedOrSelf.isMutable) xt.VarDef(id, tpe, flags).setPos(sym.pos)
        else xt.ValDef(id, tpe, flags).setPos(sym.pos)
      }

      val defCtx = tpCtx.withNewVars((symbols zip fields.map(vd => () => vd.toVariable)).toMap)

      var invariants: Seq[xt.Expr] = Seq.empty
      var methods: Seq[xt.FunDef] = Seq.empty

      for (d <- cd.impl.body) d match {
        case EmptyTree =>
          // ignore

        case t if (annotationsOf(t.symbol) contains xt.Ignore) || (t.symbol.isSynthetic) =>
          // ignore

        case ExRequiredExpression(body) =>
          invariants :+= extractTree(body)(defCtx)

        case dd @ DefDef(_, name, _, _, _, _) if dd.symbol.name.toString.startsWith("copy$default$") =>
          // @nv: FIXME - think about handling default value functions

        case t @ ExFunctionDef(fsym, tparams, vparams, tpt, rhs) =>
          methods :+= extractFunction(fsym, tparams, vparams, rhs)(defCtx)

        case t @ ExFieldDef(fsym, _, rhs) =>
          methods :+= extractFunction(fsym, Seq.empty, Seq.empty, rhs)(defCtx)

        case t @ ExLazyAccessorFunction(fsym, _, rhs) =>
          methods :+= extractFunction(fsym, Seq.empty, Seq.empty, rhs)(defCtx)

        case ExCaseClassSyntheticJunk()
           | ExConstructorDef()
           | ExLazyFieldDef()
           | ExFieldAccessorFunction() =>
             // ignore

        case ValDef(_, _, _, _) =>
          // ignore (corresponds to constructor fields)

        case d if (d.symbol.isImplicit && d.symbol.isSynthetic) =>
          // ignore

        case d if d.symbol.isVar =>
          // ignore

        case other =>
          reporter.warning(other.pos, "Could not extract tree in class: " + other + " (" + other.getClass + ")")
      }

      val optInv = if (invariants.isEmpty) None else Some(
        new xt.FunDef(SymbolIdentifier(invSymbol), Seq.empty, Seq.empty, xt.BooleanType,
          if (invariants.size == 1) invariants.head else xt.And(invariants),
          Set(xt.IsInvariant) ++ flags
        )
      )

      val allMethods = (methods ++ optInv).map(fd => fd.copy(flags = fd.flags + xt.IsMethod))

      val xcd = new xt.ClassDef(
        id,
        tparams.map(tp => xt.TypeParameterDef(tp)),
        parent,
        fields,
        allMethods.map(_.id.asInstanceOf[SymbolIdentifier]),
        flags
      ).setPos(sym.pos)

      (xcd, allMethods)
    }

    private def getSelectChain(e: Tree): List[String] = {
      def rec(e: Tree): List[Name] = e match {
        case Select(q, name) => name :: rec(q)
        case Ident(name) => List(name)
        case EmptyTree => List()
        case _ =>
          ctx.reporter.internalError("getSelectChain: unexpected Tree:\n" + e.toString)
      }
      rec(e).reverseMap(_.toString)
    }

    private def extractRef(ref: RefTree): List[String] = {
      (getSelectChain(ref.qualifier) :+ ref.name.toString).filter(_ != "<empty>")
    }

    private def extractImports(i: Import): Seq[xt.Import] = {
      val Import(expr, sels) = i

      val prefix = getSelectChain(expr)

      val allSels = sels map { prefix :+ _.name.toString }

      // Make a different import for each selector at the end of the chain
      allSels flatMap { selectors =>
        assert(selectors.nonEmpty)
        val (thePath, isWild) = selectors.last match {
          case "_" => (selectors.dropRight(1), true)
          case _   => (selectors, false)
        }

        Some(xt.Import(thePath, isWild))
      }
    }

    private def extractFunction(
      sym: Symbol,
      tparams: Seq[Symbol],
      vparams: Seq[ValDef],
      rhs: Tree,
      typeParams: Option[Seq[xt.TypeParameter]] = None
    )(implicit dctx: DefContext): xt.FunDef = {

      // Type params of the function itself
      val extparams = extractTypeParams(sym.typeParams.map(_.tpe))
      val ntparams = typeParams.getOrElse(extparams.map(sym => xt.TypeParameter.fresh(sym.name.toString)))

      val nctx = dctx.copy(tparams = dctx.tparams ++ (extparams zip ntparams).toMap)

      val newParams = sym.info.paramss.flatten.map { sym =>
        val ptpe = stainlessType(sym.tpe)(nctx, sym.pos)
        val tpe = if (sym.isByNameParam) xt.FunctionType(Seq(), ptpe) else ptpe
        val flags = annotationsOf(sym, ignoreOwner = true)
        xt.ValDef(FreshIdentifier(sym.name.toString).setPos(sym.pos), tpe, flags).setPos(sym.pos)
      }

      val returnType = stainlessType(sym.info.finalResultType)(nctx, sym.pos)

      val id = getIdentifier(sym)

      var flags = annotationsOf(sym).toSet ++
        (if (sym.isImplicit) Some(xt.Inline) else None) ++
        (if (sym.isAccessor) Some(xt.IsField(sym.isLazy)) else None)

      val body =
        if (!(flags contains xt.IsField(true))) rhs
        else rhs match {
          case Block(List(Assign(_, realBody)), _) => realBody
          case _ => outOfSubsetError(rhs, "Wrong form of lazy accessor")
        }

      val paramsMap = (vparams.map(_.symbol) zip newParams).map { case (s, vd) =>
        s -> (if (s.isByNameParam) () => xt.Application(vd.toVariable, Seq()) else () => vd.toVariable)
      }.toMap

      val fctx = dctx
        .withNewVars(paramsMap)
        .copy(tparams = dctx.tparams ++ (tparams zip ntparams))
        .copy(isExtern = dctx.isExtern || (flags contains xt.Extern))

      val finalBody = if (rhs == EmptyTree) {
        flags += xt.IsAbstract
        xt.NoTree(returnType)
      } else try {
        xt.exprOps.flattenBlocks(extractTreeOrNoTree(body)(fctx))
      } catch {
        case e: ImpureCodeEncounteredException =>
          reporter.error(e.pos, e.getMessage)
          e.printStackTrace()

          flags += xt.IsAbstract
          xt.NoTree(returnType)
      }

      val fullBody = if (fctx.isExtern) {
        xt.exprOps.withBody(finalBody, xt.NoTree(returnType).setPos(body.pos))
      } else {
        finalBody
      }

      new xt.FunDef(
        id,
        ntparams.map(tp => xt.TypeParameterDef(tp)),
        newParams,
        returnType,
        fullBody,
        flags
      ).setPos(sym.pos)
    }

    private def extractTypeParams(tps: Seq[Type]): Seq[Symbol] = tps.flatMap {
      case TypeRef(_, sym, Nil) =>
        Some(sym)
      case t =>
        outOfSubsetError(t.typeSymbol.pos, "Unhandled type for parameter: "+t)
        None
    }

    private def extractPattern(p: Tree, binder: Option[xt.ValDef] = None)(implicit dctx: DefContext): (xt.Pattern, DefContext) = p match {
      case b @ Bind(name, t @ Typed(pat, tpt)) =>
        val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(tpt), annotationsOf(b.symbol, ignoreOwner = true)).setPos(b.pos)
        val pctx = dctx.withNewVar(b.symbol, () => vd.toVariable)
        extractPattern(t, Some(vd))(pctx)

      case b @ Bind(name, pat) =>
        val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(b), annotationsOf(b.symbol, ignoreOwner = true)).setPos(b.pos)
        val pctx = dctx.withNewVar(b.symbol, () => vd.toVariable)
        extractPattern(pat, Some(vd))(pctx)

      case t @ Typed(Ident(nme.WILDCARD), tpt) =>
        extractType(tpt) match {
          case ct: xt.ClassType =>
            (xt.InstanceOfPattern(binder, ct).setPos(p.pos), dctx)

          case lt =>
            outOfSubsetError(tpt, "Invalid type "+tpt.tpe+" for .isInstanceOf")
        }

      case Ident(nme.WILDCARD) =>
        (xt.WildcardPattern(binder).setPos(p.pos), dctx)

      case s @ Select(_, b) if s.tpe.typeSymbol.isCase =>
        // case Obj =>
        extractType(s) match {
          case ct: xt.ClassType =>
            (xt.ADTPattern(binder, ct, Seq()).setPos(p.pos), dctx)
          case _ =>
            outOfSubsetError(s, "Invalid type "+s.tpe+" for .isInstanceOf")
        }

      case a @ Apply(fn, args) =>
        extractType(a) match {
          case ct: xt.ClassType =>
            val (subPatterns, subDctx) = args.map(extractPattern(_)).unzip
            val nctx = subDctx.foldLeft(dctx)(_ union _)
            (xt.ADTPattern(binder, ct, subPatterns).setPos(p.pos), nctx)

          case xt.TupleType(argsTpes) =>
            val (subPatterns, subDctx) = args.map(extractPattern(_)).unzip
            val nctx = subDctx.foldLeft(dctx)(_ union _)
            (xt.TuplePattern(binder, subPatterns).setPos(p.pos), nctx)

          case _ =>
            outOfSubsetError(a, "Invalid type "+a.tpe+" for .isInstanceOf")
        }

      case ExBigIntPattern(n: Literal) =>
        val lit = xt.IntegerLiteral(BigInt(n.value.stringValue))
        (xt.LiteralPattern(binder, lit), dctx)

      case ExInt32Literal(i)   => (xt.LiteralPattern(binder, xt.IntLiteral(i)),     dctx)
      case ExBooleanLiteral(b) => (xt.LiteralPattern(binder, xt.BooleanLiteral(b)), dctx)
      case ExUnitLiteral()     => (xt.LiteralPattern(binder, xt.UnitLiteral()),     dctx)
      case ExStringLiteral(s)  => (xt.LiteralPattern(binder, xt.StringLiteral(s)),  dctx)

      case up @ ExUnapplyPattern(t, args) =>
        val (sub, ctx) = args.map (extractPattern(_)).unzip
        val nctx = ctx.foldLeft(dctx)(_ union _)
        val id = getIdentifier(t.symbol)
        val tps = t match {
          case TypeApply(_, tps) => tps.map(extractType)
          case _ => Seq.empty
        }

        (xt.UnapplyPattern(binder, id, tps, sub).setPos(up.pos), ctx.foldLeft(dctx)(_ union _))

      case _ =>
        outOfSubsetError(p, "Unsupported pattern: " + p)
    }

    private def extractMatchCase(cd: CaseDef)(implicit dctx: DefContext): xt.MatchCase = {
      val (recPattern, ndctx) = extractPattern(cd.pat)
      val recBody             = extractTree(cd.body)(ndctx)

      if(cd.guard == EmptyTree) {
        xt.MatchCase(recPattern, None, recBody).setPos(cd.pos)
      } else {
        val recGuard = extractTree(cd.guard)(ndctx)
        xt.MatchCase(recPattern, Some(recGuard), recBody).setPos(cd.pos)
      }
    }

    private def extractTreeOrNoTree(tr: Tree)(implicit dctx: DefContext): xt.Expr = {
      try {
        extractTree(tr)
      } catch {
        case e: ImpureCodeEncounteredException =>
          if (dctx.isExtern) {
            xt.NoTree(extractType(tr)).setPos(tr.pos)
          } else {
            throw e
          }
      }
    }

    private def extractBlock(es: List[Tree])(implicit dctx: DefContext): xt.Expr = {
      val fctx = es.collect {
        case ExFunctionDef(sym, tparams, vparams, tpt, rhs) => (sym, tparams)
      }.foldLeft(dctx) { case (dctx, (sym, tparams)) =>
        val extparams = extractTypeParams(sym.typeParams.map(_.tpe))
        val tparams = extparams.map(sym => xt.TypeParameter.fresh(sym.name.toString))
        val nctx = dctx.copy(tparams = dctx.tparams ++ (extparams zip tparams).toMap)

        val paramTypes = sym.info.paramss.flatten.map { sym =>
          val ptpe = stainlessType(sym.tpe)(nctx, sym.pos)
          if (sym.isByNameParam) xt.FunctionType(Seq(), ptpe) else ptpe
        }
        val returnType = stainlessType(sym.info.finalResultType)(nctx, sym.pos)
        val name = xt.ValDef(
          getIdentifier(sym),
          xt.FunctionType(paramTypes, returnType).setPos(sym.pos),
          annotationsOf(sym)
        ).setPos(sym.pos)

        dctx.withLocalFun(sym, name, tparams.map(tp => xt.TypeParameterDef(tp)))
      }

      val (vds, vctx) = es.collect {
        case v @ ValDef(_, name, tpt, _) => (v.symbol, name, tpt)
      }.foldLeft((Map.empty[Symbol, xt.ValDef], fctx)) { case ((vds, dctx), (sym, name, tpt)) =>
        if (!sym.isMutable) {
          val vd = xt.ValDef(FreshIdentifier(name.toString), extractType(tpt)(dctx), annotationsOf(sym, ignoreOwner = true)).setPos(sym.pos)
          (vds + (sym -> vd), dctx.withNewVar(sym, () => vd.toVariable))
        } else {
          val vd = xt.VarDef(FreshIdentifier(name.toString), extractType(tpt)(dctx), annotationsOf(sym, ignoreOwner = true)).setPos(sym.pos)
          (vds + (sym -> vd), dctx.withNewMutableVar(sym, () => vd.toVariable))
        }
      }

      def rec(es: List[Tree]): xt.Expr = es match {
        case Nil => xt.UnitLiteral()

        case (e @ ExAssertExpression(contract, oerr)) :: xs =>
          val const = extractTree(contract)(vctx)
          val b     = rec(xs)
          xt.Assert(const, oerr, b).setPos(e.pos)

        case (e @ ExRequiredExpression(contract)) :: xs =>
          val pre = extractTree(contract)(vctx)
          val b   = rec(xs)
          xt.Require(pre, b).setPos(e.pos)

        case (e @ ExDecreasesExpression(rank)) :: xs =>
          val r = extractTree(rank)(vctx)
          val b = rec(xs)
          xt.Decreases(r, b).setPos(e.pos)

        case (d @ ExFunctionDef(sym, tparams, vparams, tpt, rhs)) :: xs =>
          val (vd, tdefs) = vctx.localFuns(sym)
          val fd = extractFunction(sym, tparams, vparams, rhs, typeParams = Some(tdefs.map(_.tp)))(vctx)
          val letRec = xt.LocalFunDef(vd, tdefs, xt.Lambda(fd.params, fd.fullBody).setPos(d.pos))

          rec(xs) match {
            case xt.LetRec(defs, body) => xt.LetRec(letRec +: defs, body).setPos(d.pos)
            case other => xt.LetRec(Seq(letRec), other).setPos(d.pos)
          }

        case (v @ ValDef(mods, name, tpt, _)) :: xs =>
          if (mods.isMutable) {
            xt.LetVar(vds(v.symbol), extractTree(v.rhs)(vctx), rec(xs)).setPos(v.pos)
          } else {
            xt.Let(vds(v.symbol), extractTree(v.rhs)(vctx), rec(xs)).setPos(v.pos)
          }

        case x :: Nil =>
          extractTree(x)(vctx)

        case x :: rest =>
          rec(rest) match {
            case xt.Block(elems, last) =>
              xt.Block(extractTree(x)(vctx) +: elems, last).setPos(x.pos)
            case e =>
              xt.Block(Seq(extractTree(x)(vctx)), e).setPos(x.pos)
          }
      }

      rec(es)
    }

    private def extractArgs(sym: Symbol, args: Seq[Tree])(implicit dctx: DefContext): Seq[xt.Expr] = {
      (sym.paramLists.flatten zip args.map(extractTree)).map {
        case (sym, e) => if (sym.isByNameParam) xt.Lambda(Seq.empty, e) else e
      }
    }

    private def extractTree(tr: Tree)(implicit dctx: DefContext): xt.Expr = (tr match {
      case Block(es, e) =>
        val b = extractBlock(es :+ e)
        xt.exprOps.flattenBlocks(b)

      case ExRequiredExpression(body) =>
        xt.Require(extractTree(body), xt.UnitLiteral().setPos(tr.pos))

      case ExEnsuredExpression(body, contract) =>
        val post = extractTree(contract)
        val b = extractTreeOrNoTree(body)
        val tpe = extractType(body)

        val closure = post match {
          case l: xt.Lambda => l
          case other =>
            val vd = xt.ValDef(FreshIdentifier("res"), tpe, Set.empty).setPos(post)
            xt.Lambda(Seq(vd), extractType(contract) match {
              case xt.BooleanType => post
              case _ => xt.Application(other, Seq(vd.toVariable)).setPos(post)
            }).setPos(post)
        }

        xt.Ensuring(b, closure)

      case t @ ExHoldsWithProofExpression(body, ExMaybeBecauseExpressionWrapper(proof)) =>
        val vd = xt.ValDef(FreshIdentifier("holds"), xt.BooleanType, Set.empty).setPos(tr.pos)
        val p = extractTreeOrNoTree(proof)
        val post = xt.Lambda(Seq(vd), xt.And(Seq(p, vd.toVariable))).setPos(tr.pos)
        val b = extractTreeOrNoTree(body)
        xt.Ensuring(b, post)

      case t @ ExHoldsExpression(body) =>
        val vd = xt.ValDef(FreshIdentifier("holds"), xt.BooleanType, Set.empty).setPos(tr.pos)
        val post = xt.Lambda(Seq(vd), vd.toVariable).setPos(tr.pos)
        val b = extractTreeOrNoTree(body)
        xt.Ensuring(b, post)

      // If the because statement encompasses a holds statement
      case t @ ExBecauseExpression(ExHoldsExpression(body), proof) =>
        val vd = xt.ValDef(FreshIdentifier("holds"), xt.BooleanType, Set.empty).setPos(tr.pos)
        val p = extractTreeOrNoTree(proof)
        val post = xt.Lambda(Seq(vd), xt.And(Seq(p, vd.toVariable))).setPos(tr.pos)
        val b = extractTreeOrNoTree(body)
        xt.Ensuring(b, post)

      case t @ ExComputesExpression(body, expected) =>
        val b = extractTreeOrNoTree(body).setPos(body.pos)
        val expectedExpr = extractTreeOrNoTree(expected).setPos(expected.pos)
        val vd = xt.ValDef(FreshIdentifier("res"), extractType(body), Set.empty).setPos(tr.pos)
        val post = xt.Lambda(Seq(vd), xt.Equals(vd.toVariable, expectedExpr)).setPos(tr.pos)
        xt.Ensuring(b, post)

      case ExPreExpression(f) =>
        xt.Pre(extractTree(f))

      case t @ ExBigLengthExpression(input) =>
        xt.StringLength(extractTreeOrNoTree(input))

      case t @ ExBigSubstringExpression(input, start) =>
        val in = extractTreeOrNoTree(input)
        val st = extractTreeOrNoTree(start)
        val vd = xt.ValDef(FreshIdentifier("s", true), xt.StringType, Set.empty)
        xt.Let(vd, in, xt.SubString(vd.toVariable, st, xt.StringLength(vd.toVariable)))

      case t @ ExBigSubstring2Expression(input, start, end) =>
        val in = extractTreeOrNoTree(input)
        val st = extractTreeOrNoTree(start)
        val en = extractTreeOrNoTree(end)
        xt.SubString(in, st, en)

      case ExArrayLiteral(tpe, args) =>
        xt.FiniteArray(args.map(extractTree), extractType(tpe)(dctx, tr.pos))

      case s @ ExCaseObject(sym) =>
        extractType(s) match {
          case ct: xt.ClassType => xt.ClassConstructor(ct, Seq.empty)
          case tpe => outOfSubsetError(tr, "Unexpected class constructor type: " + tpe)
        }

      case ExTuple(tpes, exprs) =>
        xt.Tuple(exprs map extractTree)

      case ExOldExpression(t) => t match {
        case t: This => xt.Old(extractTree(t))
        case v if dctx.isVariable(v.symbol) =>
          xt.Old(dctx.vars.get(v.symbol).orElse(dctx.mutableVars.get(v.symbol)).get())
        case _ => outOfSubsetError(tr, "Old is only defined on `this` and variables")
      }

      case ExErrorExpression(str, tpt) =>
        xt.Error(extractType(tpt), str)

      case ExTupleExtract(tuple, index) =>
        xt.TupleSelect(extractTree(tuple), index)

      /**
       * XLang Extractors
       */

      case a @ ExAssign(sym, rhs) =>
        dctx.mutableVars.get(sym) match {
          case Some(fun) =>
            xt.Assignment(fun().setPos(a.pos), extractTree(rhs))

          case None =>
            outOfSubsetError(a, "Undeclared variable.")
        }

      case wh @ ExWhile(cond, body) =>
        xt.While(extractTree(cond), extractTree(body), None)

      case wh @ ExWhileWithInvariant(cond, body, inv) =>
        xt.While(extractTree(cond), extractTree(body), Some(extractTree(inv)))

      case update @ ExUpdate(lhs, index, newValue) =>
        xt.ArrayUpdate(extractTree(lhs), extractTree(index), extractTree(newValue))

      case ExBigIntLiteral(n: Literal) =>
        xt.IntegerLiteral(BigInt(n.value.stringValue))

      case ExBigIntLiteral(n) => outOfSubsetError(tr, "Non-literal BigInt constructor")

      case ExIntToBigInt(tree) =>
        extractTree(tree) match {
          case xt.IntLiteral(n) => xt.IntegerLiteral(BigInt(n))
          case _ => outOfSubsetError(tr, "Conversion from Int to BigInt")
        }

      case ExRealLiteral(n, d) =>
        (extractTree(n), extractTree(d)) match {
          case (xt.IntegerLiteral(n), xt.IntegerLiteral(d)) => xt.FractionLiteral(n, d)
          case _ => outOfSubsetError(tr, "Real not build from literals")
        }

      case ExRealIntLiteral(n) =>
        extractTree(n) match {
          case xt.IntegerLiteral(n) => xt.FractionLiteral(n, 1)
          case _ => outOfSubsetError(tr, "Real not build from literals")
        }

      case ExInt32Literal(v) => xt.IntLiteral(v)
      case ExBooleanLiteral(v) => xt.BooleanLiteral(v)
      case ExUnitLiteral() => xt.UnitLiteral()
      case ExCharLiteral(c) => xt.CharLiteral(c)
      case ExStringLiteral(s) => xt.StringLiteral(s)

      case ExLocally(body) => extractTree(body)

      case ExTyped(e, _) =>
        // TODO: refine type here?
        extractTree(e)

      case ex @ ExIdentifier(sym, tpt) =>
        dctx.vars.get(sym).orElse(dctx.mutableVars.get(sym)) match {
          case Some(builder) => builder().setPos(ex.pos)
          case None => dctx.localFuns.get(sym) match {
            case Some((vd, tparams)) => xt.ApplyLetRec(vd.toVariable, tparams.map(_.tp), Seq.empty)
            case None => xt.FunctionInvocation(getIdentifier(sym), Seq.empty, Seq.empty)
          }
        }

      case hole @ ExHoleExpression(tpt, exprs) =>
        // FIXME: we ignore [[exprs]] for now...
        xt.Hole(extractType(tpt))

      case chs @ ExChooseExpression(body) =>
        extractTree(body) match {
          case xt.Lambda(Seq(vd), body) => xt.Choose(vd, body)
          case _ => outOfSubsetError(tr, "Unexpected choose definition")
        }

      case l @ ExLambdaExpression(args, body) =>
        val vds = args map(vd => xt.ValDef(
          FreshIdentifier(vd.symbol.name.toString),
          extractType(vd.tpt),
          annotationsOf(vd.symbol, ignoreOwner = true)
        ).setPos(vd.pos))

        val newVars = (args zip vds).map { case (vd, lvd) =>
          vd.symbol -> (() => lvd.toVariable)
        }

        val exBody = extractTree(body)(dctx.withNewVars(newVars))
        xt.Lambda(vds, exBody)

      case ExForallExpression(args, body) =>
        val vds = args map { case (tpt, sym) =>
          xt.ValDef(FreshIdentifier(sym.name.toString), extractType(tpt), annotationsOf(sym, ignoreOwner = true)).setPos(sym.pos)
        }

        val newVars = (args zip vds).map { case ((_, sym), lvd) =>
          sym -> (() => lvd.toVariable)
        }

        val exBody = extractTree(body)(dctx.withNewVars(newVars))
        xt.Forall(vds, exBody)

      case ExFiniteMap(tptFrom, tptTo, args) =>
        val to = extractType(tptTo)
        val pairs = args.map {
          case ExTuple(_, Seq(key, value)) =>
            (extractTree(key), extractTree(value))
          case tree =>
            val ex = extractTree(tree)
            (xt.TupleSelect(ex, 1), xt.TupleSelect(ex, 2))
        }

        val somePairs = pairs.map { case (key, value) =>
          key -> xt.ClassConstructor(
            xt.ClassType(getIdentifier(someSymbol), Seq(to)).setPos(tr.pos),
            Seq(value)
          ).setPos(tr.pos)
        }

        val dflt = xt.ClassConstructor(
          xt.ClassType(getIdentifier(noneSymbol), Seq(to)).setPos(tr.pos),
          Seq.empty
        ).setPos(tr.pos)

        val optTo = xt.ClassType(getIdentifier(optionSymbol), Seq(to))
        xt.FiniteMap(somePairs, dflt, extractType(tptFrom), optTo)

      case ExFiniteSet(tpt, args) =>
        xt.FiniteSet(args.map(extractTree), extractType(tpt))

      case ExFiniteBag(tpt, args) =>
        xt.FiniteBag(args.map {
          case ExTuple(_, Seq(key, value)) =>
            (extractTree(key), extractTree(value))
          case tree =>
            val ex = extractTree(tree)
            (xt.TupleSelect(ex, 1), xt.TupleSelect(ex, 2))
        }, extractType(tpt))

      case ExCaseClassConstruction(tpt, args) =>
        extractType(tpt) match {
          case ct: xt.ClassType => xt.ClassConstructor(ct, args.map(extractTree))
          case _ => outOfSubsetError(tr, "Construction of a non-class type.")
        }

      case ExNot(e)        => xt.Not(extractTree(e))
      case ExUMinus(e)     => xt.UMinus(extractTree(e))
      case ExBVNot(e)      => xt.BVNot(extractTree(e))

      case ExNotEquals(l, r) => xt.Not(((extractTree(l), extractType(l), extractTree(r), extractType(r)) match {
        case (xt.IntLiteral(i), _, e, xt.IntegerType) => xt.Equals(xt.IntegerLiteral(i), e)
        case (e, xt.IntegerType, xt.IntLiteral(i), _) => xt.Equals(e, xt.IntegerLiteral(i))
        case (e1, _, e2, _) => xt.Equals(e1, e2)
      }).setPos(tr.pos))

      case ExEquals(l, r) => (extractTree(l), extractType(l), extractTree(r), extractType(r)) match {
        case (xt.IntLiteral(i), _, e, xt.IntegerType) => xt.Equals(xt.IntegerLiteral(i), e)
        case (e, xt.IntegerType, xt.IntLiteral(i), _) => xt.Equals(e, xt.IntegerLiteral(i))
        case (e1, _, e2, _) => xt.Equals(e1, e2)
      }

      case ExArrayFill(baseType, length, defaultValue) =>
        val lengthRec = extractTree(length)
        val defaultValueRec = extractTree(defaultValue)
        xt.LargeArray(Map.empty, extractTree(defaultValue), extractTree(length), extractType(baseType))

      case ExIfThenElse(t1,t2,t3) =>
        xt.IfExpr(extractTree(t1), extractTree(t2), extractTree(t3))

      case ExAsInstanceOf(expr, tt) =>
        extractType(tt) match {
          case ct: xt.ClassType => xt.AsInstanceOf(extractTree(expr), ct)
          case _ => outOfSubsetError(tr, "asInstanceOf can only cast to class types")
        }

      case ExIsInstanceOf(expr, tt) =>
        extractType(tt) match {
          case ct: xt.ClassType => xt.IsInstanceOf(extractTree(expr), ct)
          case _ => outOfSubsetError(tr, "isInstanceOf can only be used with class types")
        }

      case pm @ ExPatternMatching(sel, cses) =>
        val rs = extractTree(sel)
        val rc = cses.map(extractMatchCase)
        xt.MatchExpr(rs, rc)

      case t: This =>
        extractType(t) match {
          case ct: xt.ClassType => xt.This(ct)
          case _ => outOfSubsetError(t, "Invalid usage of `this`")
        }

      case aup @ ExArrayUpdated(ar, k, v) =>
        xt.ArrayUpdated(extractTree(ar), extractTree(k), extractTree(v))

      case l @ ExListLiteral(tpe, elems) =>
        val rtpe = extractType(tpe)
        val cons = xt.ClassType(getIdentifier(consSymbol), Seq(rtpe))
        val nil  = xt.ClassType(getIdentifier(nilSymbol),  Seq(rtpe))

        elems.foldRight(xt.ClassConstructor(nil, Seq())) {
          case (e, ls) => xt.ClassConstructor(cons, Seq(extractTree(e), ls))
        }

      case ExImplies(lhs, rhs) =>
        xt.Implies(extractTree(lhs), extractTree(rhs))

      case c @ ExCall(rec, sym, tps, args) => rec match {
        case None =>
          dctx.localFuns.get(sym) match {
            case None =>
              xt.FunctionInvocation(getIdentifier(sym), tps.map(extractType), extractArgs(sym, args))
            case Some((vd, tparams)) =>
              xt.ApplyLetRec(vd.toVariable, tparams.map(_.tp), extractArgs(sym, args))
          }

        case Some(lhs) => extractType(lhs) match {
          case ct: xt.ClassType =>
            val isMethod = sym.isMethod &&
              !sym.isCaseAccessor && !sym.accessedOrSelf.isCaseAccessor &&
              !(sym.isAccessor && sym.owner.isImplicit)

            if (isMethod) xt.MethodInvocation(
              extractTree(lhs),
              getIdentifier(sym),
              tps.map(extractType),
              extractArgs(sym, args)
            ) else args match {
              case Seq() =>
                xt.ClassSelector(extractTree(lhs), getIdentifier(sym))
              case Seq(rhs) =>
                val getter = sym.accessed.getterIn(sym.owner)
                xt.FieldAssignment(extractTree(lhs), getIdentifier(getter), extractTree(rhs))
              case _ => outOfSubsetError(tr, "Unexpected call")
            }

          case ft: xt.FunctionType =>
            xt.Application(extractTree(lhs), args.map(extractTree))

          case tpe => (tpe, sym.name.decode.toString, args) match {
            case (xt.StringType, "+", Seq(rhs)) => xt.StringConcat(extractTree(lhs), extractTree(rhs))
            case (xt.IntegerType | xt.BVType(_) | xt.RealType, "+", Seq(rhs)) => xt.Plus(extractTree(lhs), extractTree(rhs))

            case (xt.SetType(_), "+",  Seq(rhs)) => xt.SetAdd(extractTree(lhs), extractTree(rhs))
            case (xt.SetType(_), "++", Seq(rhs)) => xt.SetUnion(extractTree(lhs), extractTree(rhs))
            case (xt.SetType(_), "&",  Seq(rhs)) => xt.SetIntersection(extractTree(lhs), extractTree(rhs))
            case (xt.SetType(_), "--", Seq(rhs)) => xt.SetDifference(extractTree(lhs), extractTree(rhs))
            case (xt.SetType(_), "subsetOf", Seq(rhs)) => xt.SubsetOf(extractTree(lhs), extractTree(rhs))
            case (xt.SetType(_), "contains", Seq(rhs)) => xt.ElementOfSet(extractTree(rhs), extractTree(lhs))

            case (xt.BagType(_), "+",   Seq(rhs)) => xt.BagAdd(extractTree(lhs), extractTree(rhs))
            case (xt.BagType(_), "++",  Seq(rhs)) => xt.BagUnion(extractTree(lhs), extractTree(rhs))
            case (xt.BagType(_), "&",   Seq(rhs)) => xt.BagIntersection(extractTree(lhs), extractTree(rhs))
            case (xt.BagType(_), "--",  Seq(rhs)) => xt.BagDifference(extractTree(lhs), extractTree(rhs))
            case (xt.BagType(_), "get", Seq(rhs)) => xt.MultiplicityInBag(extractTree(rhs), extractTree(lhs))

            case (xt.ArrayType(_), "apply",   Seq(rhs))          => xt.ArraySelect(extractTree(lhs), extractTree(rhs))
            case (xt.ArrayType(_), "length",  Seq())             => xt.ArrayLength(extractTree(lhs))
            case (xt.ArrayType(_), "updated", Seq(index, value)) => xt.ArrayUpdated(extractTree(lhs), extractTree(index), extractTree(value))
            case (xt.ArrayType(_), "clone",   Seq())             => extractTree(lhs)

            case (xt.MapType(_, _), "get", Seq(rhs)) =>
              xt.MapApply(extractTree(lhs), extractTree(rhs))

            case (xt.MapType(_, xt.ClassType(_, Seq(to))), "apply", Seq(rhs)) =>
              val (l, r) = (extractTree(lhs), extractTree(rhs))
              val someTpe = xt.ClassType(getIdentifier(someSymbol), Seq(to)).setPos(tr.pos)
              xt.Assert(
                xt.IsInstanceOf(xt.MapApply(l, r).setPos(tr.pos), someTpe).setPos(tr.pos),
                Some("Map undefined at this index"),
                xt.ClassSelector(
                  xt.AsInstanceOf(xt.MapApply(l, r).setPos(tr.pos), someTpe),
                  getIdentifier(someSymbol.caseFieldAccessors.head)
                ).setPos(tr.pos)
              )

            case (xt.MapType(_, xt.ClassType(_, Seq(to))), "isDefinedAt" | "contains", Seq(rhs)) =>
              xt.Not(xt.Equals(
                xt.MapApply(extractTree(lhs), extractTree(rhs)).setPos(tr.pos),
                xt.ClassConstructor(
                  xt.ClassType(getIdentifier(noneSymbol).setPos(tr.pos), Seq(to)),
                  Seq()
                ).setPos(tr.pos)
              ).setPos(tr.pos))

            case (xt.MapType(_, xt.ClassType(_, Seq(to))), "updated" | "+", Seq(key, value)) =>
              xt.MapUpdated(
                extractTree(lhs), extractTree(key),
                xt.ClassConstructor(
                  xt.ClassType(getIdentifier(someSymbol), Seq(to)).setPos(tr.pos),
                  Seq(extractTree(value))
                ).setPos(tr.pos)
              )

            case (xt.MapType(_, xt.ClassType(_, Seq(to))), "+", Seq(rhs)) =>
              val value = extractTree(rhs)
              xt.MapUpdated(
                extractTree(lhs), xt.TupleSelect(value, 1).setPos(tr.pos),
                xt.ClassConstructor(
                  xt.ClassType(getIdentifier(someSymbol), Seq(to)).setPos(tr.pos),
                  Seq(xt.TupleSelect(value, 2).setPos(tr.pos))
                ).setPos(tr.pos)
              )

            case (xt.MapType(_, xt.ClassType(_, Seq(to))), "++", Seq(rhs)) =>
              extractTree(rhs) match {
                case xt.FiniteMap(pairs,  default, keyType, valueType) =>
                  pairs.foldLeft(extractTree(lhs)) { case (map, (k, v)) =>
                    xt.MapUpdated(map, k, v).setPos(tr.pos)
                  }

                case _ => outOfSubsetError(tr, "Can't extract map union with non-finite map")
              }

            case (xt.MapType(_, xt.ClassType(_, Seq(to))), "getOrElse", Seq(key, orElse)) =>
              xt.MethodInvocation(
                xt.MapApply(extractTree(lhs), extractTree(key)).setPos(tr.pos),
                getIdentifier(optionSymbol.tpe.member(TermName("getOrElse"))),
                Seq.empty,
                Seq(xt.Lambda(Seq(), extractTree(orElse)).setPos(tr.pos))
              )

            case (_, "-",   Seq(rhs)) => xt.Minus(extractTree(lhs), extractTree(rhs))
            case (_, "*",   Seq(rhs)) => xt.Times(extractTree(lhs), extractTree(rhs))
            case (_, "%",   Seq(rhs)) => xt.Remainder(extractTree(lhs), extractTree(rhs))
            case (_, "mod", Seq(rhs)) => xt.Modulo(extractTree(lhs), extractTree(rhs))
            case (_, "/",   Seq(rhs)) => xt.Division(extractTree(lhs), extractTree(rhs))
            case (_, ">",   Seq(rhs)) => xt.GreaterThan(extractTree(lhs), extractTree(rhs))
            case (_, ">=",  Seq(rhs)) => xt.GreaterEquals(extractTree(lhs), extractTree(rhs))
            case (_, "<",   Seq(rhs)) => xt.LessThan(extractTree(lhs), extractTree(rhs))
            case (_, "<=",  Seq(rhs)) => xt.LessEquals(extractTree(lhs), extractTree(rhs))

            case (_, "|",   Seq(rhs)) => xt.BVOr(extractTree(lhs), extractTree(rhs))
            case (_, "&",   Seq(rhs)) => xt.BVAnd(extractTree(lhs), extractTree(rhs))
            case (_, "^",   Seq(rhs)) => xt.BVXor(extractTree(lhs), extractTree(rhs))
            case (_, "<<",  Seq(rhs)) => xt.BVShiftLeft(extractTree(lhs), extractTree(rhs))
            case (_, ">>",  Seq(rhs)) => xt.BVAShiftRight(extractTree(lhs), extractTree(rhs))
            case (_, ">>>", Seq(rhs)) => xt.BVLShiftRight(extractTree(lhs), extractTree(rhs))

            case (_, "&&",  Seq(rhs)) => xt.And(extractTree(lhs), extractTree(rhs))
            case (_, "||",  Seq(rhs)) => xt.Or(extractTree(lhs), extractTree(rhs))

            case (tpe, name, args) =>
              outOfSubsetError(tr, "Unknown call to " + name +
                s" on $lhs (${extractType(lhs)}) with arguments $args of type ${args.map(a => extractType(a))}")
          }
        }
      }

      // default behaviour is to complain :)
      case _ => outOfSubsetError(tr, "Could not extract " + tr + " (Scala tree of type "+tr.getClass+")")
    }).setPos(tr.pos)

    private def extractType(t: Tree)(implicit dctx: DefContext): xt.Type = {
      extractType(t.tpe)(dctx, t.pos)
    }

    private def extractType(tpt: Type)(implicit dctx: DefContext, pos: Position): xt.Type = tpt match {
      case tpe if tpe == CharClass.tpe    => xt.CharType
      case tpe if tpe == IntClass.tpe     => xt.Int32Type
      case tpe if tpe == BooleanClass.tpe => xt.BooleanType
      case tpe if tpe == UnitClass.tpe    => xt.UnitType
      case tpe if tpe == NothingClass.tpe => xt.Untyped

      case ct: ConstantType => extractType(ct.value.tpe)

      case TypeRef(_, sym, _) if isBigIntSym(sym) => xt.IntegerType
      case TypeRef(_, sym, _) if isRealSym(sym)   => xt.RealType
      case TypeRef(_, sym, _) if isStringSym(sym) => xt.StringType

      case TypeRef(_, sym, btt :: Nil) if isScalaSetSym(sym) =>
        outOfSubsetError(pos, "Scala's Set API is no longer extracted. Make sure you import leon.lang.Set that defines supported Set operations.")

      case TypeRef(_, sym, List(a,b)) if isScalaMapSym(sym) =>
        outOfSubsetError(pos, "Scala's Map API is no longer extracted. Make sure you import leon.lang.Map that defines supported Map operations.")

      case TypeRef(_, sym, btt :: Nil) if isSetSym(sym) =>
        xt.SetType(extractType(btt))

      case TypeRef(_, sym, btt :: Nil) if isBagSym(sym) =>
        xt.BagType(extractType(btt))

      case TypeRef(_, sym, List(ftt,ttt)) if isMapSym(sym) =>
        xt.MapType(extractType(ftt), xt.ClassType(getIdentifier(optionSymbol), Seq(extractType(ttt))))

      case TypeRef(_, sym, List(t1,t2)) if isTuple2(sym) =>
        xt.TupleType(Seq(extractType(t1),extractType(t2)))

      case TypeRef(_, sym, List(t1,t2,t3)) if isTuple3(sym) =>
        xt.TupleType(Seq(extractType(t1),extractType(t2),extractType(t3)))

      case TypeRef(_, sym, List(t1,t2,t3,t4)) if isTuple4(sym) =>
        xt.TupleType(Seq(extractType(t1),extractType(t2),extractType(t3),extractType(t4)))

      case TypeRef(_, sym, List(t1,t2,t3,t4,t5)) if isTuple5(sym) =>
        xt.TupleType(Seq(extractType(t1),extractType(t2),extractType(t3),extractType(t4),extractType(t5)))

      case TypeRef(_, sym, btt :: Nil) if isArrayClassSym(sym) =>
        xt.ArrayType(extractType(btt))

      case TypeRef(_, sym, subs) if subs.size >= 1 && isFunction(sym, subs.size - 1) =>
        val from = subs.init
        val to   = subs.last
        xt.FunctionType(from map extractType, extractType(to))

      case TypeRef(_, sym, tps) if isByNameSym(sym) =>
        extractType(tps.head)

      case TypeRef(_, sym, _) if sym.isAbstractType =>
        if (dctx.tparams contains sym) {
          dctx.tparams(sym)
        } else {
          outOfSubsetError(pos, "Unknown type parameter "+sym)
        }

      case tr @ TypeRef(_, sym, tps) if sym.isClass =>
        xt.ClassType(getIdentifier(sym), tps.map(extractType))

      case tt: ThisType =>
        xt.ClassType(getIdentifier(tt.sym), tt.sym.typeParams.map(dctx.tparams))

      case SingleType(pre, sym) if sym.isModule =>
        xt.ClassType(getIdentifier(sym.moduleClass), Nil)

      case SingleType(_, sym) if sym.isTerm =>
        extractType(tpt.widen)

      case RefinedType(parents, defs) if defs.isEmpty =>
        /**
         * For cases like if(a) e1 else e2 where
         *   e1 <: C1,
         *   e2 <: C2,
         *   with C1,C2 <: C
         *
         * Scala might infer a type for C such as: Product with Serializable with C
         * we generalize to the first known type, e.g. C.
         */
        parents.filter(ptpe => !ignoreClasses(ptpe)).headOption.map(extractType) match {
          case Some(tpe) =>
            tpe

          case None =>
            outOfSubsetError(tpt.typeSymbol.pos, "Could not extract refined type: "+tpt+" ("+tpt.getClass+")")
        }

      case AnnotatedType(_, tpe) => extractType(tpe)

      case _ =>
        if (tpt ne null) {
          outOfSubsetError(tpt.typeSymbol.pos, "Could not extract type: "+tpt+" ("+tpt.getClass+")")
        } else {
          outOfSubsetError(NoPosition, "Tree with null-pointer as type found")
        }
    }
  }
}
