package stainless
package frontends.dotc

import dotty.tools.dotc._
import ast.tpd
import ast.Trees._
import core.Contexts._
import core.Constants._
import core.Names._
import core.StdNames._
import core.Symbols._
import core.Types._
import core.Flags._

trait ASTExtractors {

  protected implicit val ctx: Context

  def classFromName(nameStr: String): ClassSymbol = ctx.requiredClass(typeName(nameStr))

  // Well-known symbols that we match on

  protected lazy val tuple2Sym    = classFromName("scala.Tuple2")
  protected lazy val tuple3Sym    = classFromName("scala.Tuple3")
  protected lazy val tuple4Sym    = classFromName("scala.Tuple4")
  protected lazy val tuple5Sym    = classFromName("scala.Tuple5")
  protected lazy val scalaMapSym  = classFromName("scala.collection.immutable.Map")
  protected lazy val scalaSetSym  = classFromName("scala.collection.immutable.Set")
  protected lazy val setSym       = classFromName("stainless.lang.Set")
  protected lazy val mapSym       = classFromName("stainless.lang.Map")
  protected lazy val bagSym       = classFromName("stainless.lang.Bag")
  protected lazy val realSym      = classFromName("stainless.lang.Real")

  protected lazy val optionSymbol = classFromName("stainless.lang.Option")
  protected lazy val someSymbol   = classFromName("stainless.lang.Some")
  protected lazy val noneSymbol   = classFromName("stainless.lang.None")

  protected lazy val listSymbol = classFromName("stainless.collection.List")
  protected lazy val consSymbol = classFromName("stainless.collection.Cons")
  protected lazy val nilSymbol  = classFromName("stainless.collection.Nil")

  protected lazy val optionClassSym     = classFromName("scala.Option")
  protected lazy val arraySym           = classFromName("scala.Array")
  protected lazy val someClassSym       = classFromName("scala.Some")
//  protected lazy val byNameSym          = classFromName("scala.<byname>")
  protected lazy val bigIntSym          = classFromName("scala.math.BigInt")
  protected lazy val stringSym          = classFromName("java.lang.String")

  protected def functionTraitSym(i:Int) = {
    require(0 <= i && i <= 22)
    classFromName("scala.Function" + i)
  }

  def isTuple2(sym: Symbol) : Boolean = sym == tuple2Sym
  def isTuple3(sym: Symbol) : Boolean = sym == tuple3Sym
  def isTuple4(sym: Symbol) : Boolean = sym == tuple4Sym
  def isTuple5(sym: Symbol) : Boolean = sym == tuple5Sym

  object TupleSymbol {
    private val tupleSyms = Seq(tuple2Sym, tuple3Sym, tuple4Sym, tuple5Sym)
    def unapply(sym: Symbol): Option[Int] = {
      val idx = tupleSyms.indexOf(sym)
      if (idx >= 0) {
        Some(idx + 2)
      } else {
        None
      }
    }

    def unapply(tree: tpd.Tree): Option[Int] = unapply(tree.tpe.typeSymbol)
  }

  def isBigIntSym(sym: Symbol) : Boolean = getResolvedTypeSym(sym) == bigIntSym

  def isStringSym(sym: Symbol) : Boolean = getResolvedTypeSym(sym) match { case `stringSym` => true case _ => false }

//  def isByNameSym(sym : Symbol) : Boolean = getResolvedTypeSym(sym) == byNameSym

  // Resolve type aliases
  def getResolvedTypeSym(sym: Symbol): Symbol = {
    if (sym.isAliasType) {
      getResolvedTypeSym(sym.info.resultType.typeSymbol)
    } else {
      sym
    }
  }

  def isSetSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == setSym
  }

  def isMapSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == mapSym
  }

  def isBagSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == bagSym
  }

  def isRealSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == realSym
  }

  def isScalaSetSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == scalaSetSym
  }

  def isScalaMapSym(sym: Symbol) : Boolean = {
    getResolvedTypeSym(sym) == scalaMapSym
  }

  def isOptionClassSym(sym : Symbol) : Boolean = {
    sym == optionClassSym || sym == someClassSym
  }

  def isFunction(sym: Symbol, i: Int) : Boolean = {
    0 <= i && i <= 22 && sym == functionTraitSym(i)
  }

  def isArrayClassSym(sym: Symbol): Boolean = sym == arraySym

  def hasIntType(t: tpd.Tree) = {
    val tpe = t.tpe.widen
    tpe =:= defn.IntClass.info
  }

  def hasBigIntType(t: tpd.Tree) = isBigIntSym(t.tpe.typeSymbol)

  def hasStringType(t: tpd.Tree) = isStringSym(t.tpe.typeSymbol)

//  def hasRealType(t: tpd.Tree) = isRealSym(t.tpe.typeSymbol)

  import AuxiliaryExtractors._
  import ExpressionExtractors._
  import StructuralExtractors._

  // Actual extractors

  object AuxiliaryExtractors {
    object ExSelected {
      def unapplySeq(select: tpd.Select): Option[Seq[String]] = select match {
        case Select(This(tname), name) =>
          Some(Seq(tname.toString, name.toString))
        case Select(from: tpd.Select, name) =>
          unapplySeq(from).map(seq => seq :+ name.toString)
        case Select(from: tpd.Ident, name) =>
          Some(Seq(from.toString, name.toString))
        case _ => None
      }
    }

    object ExNamed {
      def unapply(name: Name): Option[String] = Some(name.toString)
    }

    object ExSymbol {
      def unapplySeq(arg: Any): Option[Seq[String]] = arg match {
        case (t: Tree[_]) => Some(t.symbol.fullName.toString.split('.').toSeq)
        case sym: Symbol => Some(sym.fullName.toString.split('.').toSeq)
      }
    }
  }

  object ExpressionExtractors {

    object ExIdentifier {
      def unapply(tree: tpd.Ident): Option[(Symbol, tpd.Tree)] = tree match {
        case i: tpd.Ident => Some((i.symbol, i))
        case _ => None
      }
    }

    object ExThis {
      def unapply(tree: tpd.This): Option[(Symbol, tpd.Tree)] = tree match {
        case thiz: tpd.This => Some((thiz.symbol, thiz))
        case _ => None
      }
    }

    object ExTyped {
      def unapply(tree: tpd.Typed): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case Typed(e,t) => Some((e, t))
        case _ => None
      }
    }

    object ExLiteral {
      def unapply(tree: tpd.Literal): Boolean = true
    }

    object ExBooleanLiteral {
      def unapply(tree: tpd.Literal): Option[Boolean] = tree match {
        case Literal(Constant(true)) => Some(true)
        case Literal(Constant(false)) => Some(false)
        case _ => None
      }
    }

    object ExCharLiteral {
      def unapply(tree: tpd.Literal): Option[Char] = tree match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.CharClass => Some(c.charValue)
        case _ => None
      }
    }

    object ExInt32Literal {
      def unapply(tree: tpd.Literal): Option[Int] = tree match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.IntClass => Some(c.intValue)
        case _ => None
      }
    }

    object ExBigIntLiteral {
      def unapply(tree: tpd.Tree): Option[tpd.Tree] = tree match {
        case Apply(ExSymbol("scala", "package", "BigInt$", "apply"), Seq(i)) => Some(i)
        case Apply(ExSymbol("stainless", "lang", "package", "BigInt$", "apply"), Seq(i)) => Some(i)
        case _ => None
      }
    }

    object ExRealLiteral {
      def unapply(tree: tpd.Tree): Option[Seq[tpd.Tree]] = tree match {
        case Apply(ExSymbol("stainless", "lang", "Real$", "apply"), args) => Some(args)
        case _ => None
      }
    }

    object ExUnitLiteral {
      def unapply(tree: tpd.Literal): Boolean = tree match {
        case Literal(c @ Constant(_)) if c.tpe.classSymbol == defn.UnitClass => true
        case _ => false
      }
    }

    /** Returns a string literal from a constant string literal. */
    object ExStringLiteral {
      def unapply(tree: tpd.Tree): Option[String] = tree  match {
        case Literal(c @ Constant(i)) if c.tpe.classSymbol == defn.StringClass =>
          Some(c.stringValue)
        case _ =>
          None
      }
    }

    object ExCall {
      def unapply(tree: tpd.Tree): Option[(Option[tpd.Tree], Symbol, Seq[tpd.Tree], Seq[tpd.Tree])] = tree match {
        case tree @ Select(qualifier, _) =>
          Some((Some(qualifier), tree.symbol, Nil, Nil))

        case tree @ Apply(id: tpd.Ident, args) =>
          Some((None, id.symbol, Nil, args))

        case tree @ Apply(select @ Select(qualifier, _), args) =>
          Some((Some(qualifier), select.symbol, Nil, args))

        case tree @ TypeApply(id: tpd.Ident, tps) =>
          Some((None, id.symbol, tps, Nil))

        case tree @ TypeApply(select @ Select(qualifier, _), tps) =>
          Some((Some(qualifier), select.symbol, tps, Nil))

        case tree @ Apply(ExCall(caller, sym, tps, args), newArgs) =>
          Some((caller, sym, tps, args ++ newArgs))

        case tree @ TypeApply(ExCall(caller, sym, tps, args), newTps) =>
          Some((caller, sym, tps ++ newTps, args))

        case _ =>
          None
      }
    }

    object ExADT {
      def unapply(tree: tpd.Tree): Option[(Type, Seq[tpd.Tree])] = tree match {
        case Apply(Select(New(tpt), CONSTRUCTOR), args) =>
          Some((tpt.tpe, args))

        case _ =>
          None
      }
    }

    object ExTuple {
      def unapply(tree: tpd.Tree): Option[Seq[tpd.Tree]] = tree match {
        case Apply(Select(New(TupleSymbol(i)), nme.CONSTRUCTOR), args) if args.size == i =>
          Some(args)
        case Apply(TypeApply(Select(
          Apply(TypeApply(ExSymbol("scala", "Predef$", "ArrowAssoc"), Seq(_)), Seq(from)),
          ExNamed("$minus$greater")
        ), Seq(_)), Seq(to)) => Some(Seq(from, to))
        case _ => None
      }
    }

    object ExTupleSelect {
      private val Pattern = """_(\d{1,2})""".r

      def unapply(tree: tpd.Tree): Option[(tpd.Tree, Int)] = tree match {
        case Select(tuple @ TupleSymbol(i), ExNamed(Pattern(n))) if n.toInt <= i =>
          Some((tuple, n.toInt))
        case _ => None
      }
    }
  }

  object StructuralExtractors {

    object ExObjectDef {
      def unapply(td: tpd.TypeDef): Boolean = {
        val sym = td.symbol
        td.isClassDef && ((sym is ModuleClass) || (sym is Package)) && !(sym is Synthetic) && !(sym is Case)
      }
    }

    object ExClassDef {
      def unapply(td: tpd.TypeDef): Boolean = {
        val sym = td.symbol
        td.isClassDef //&& ((sym is Abstract) || (sym is Case) || (sym is Implicit))
      }
    }

    object ExFunctionDef {
      def unapply(dd: tpd.DefDef): Option[(Symbol, Seq[tpd.TypeDef], Seq[tpd.ValDef], Type, tpd.Tree)] = dd match {
        case DefDef(name, tparams, vparamss, tpt, rhs) if (
          name != nme.CONSTRUCTOR && !dd.symbol.is(Accessor) &&
          !dd.symbol.is(Synthetic)
        ) => Some((dd.symbol, tparams, vparamss.flatten, tpt.tpe, dd.rhs))

        case _ => None
      }
    }

    object ExFieldDef {
      def unapply(tree: tpd.ValOrDefDef): Option[(Symbol, Type, tpd.Tree)] = {
        val sym = tree.symbol
        tree match {
          case vd @ ValDef(_, tpt, _) if (
            !(sym is CaseAccessor) && !(sym is ParamAccessor) &&
            !(sym is Lazy) && !(sym is Synthetic) && !(sym is Accessor) && !(sym is Mutable)
          ) => Some((sym, tpt.tpe, vd.rhs))

          case dd @ DefDef(_, _, _, tpt, _) if (
            (sym is Stable) && (sym is Accessor) &&
            (sym.name != nme.CONSTRUCTOR) // TODO: && (sym.accessed == NoSymbol)
          ) => Some((sym, tpt.tpe, tpd.EmptyTree))

          case _ => None
        }
      }
    }

    object ExLazyFieldDef {
      def unapply(tree: tpd.DefDef): Option[(Symbol, Type, tpd.Tree)] = {
        val sym = tree.symbol
        tree match {
          case DefDef(name, _, Seq() | Seq(_), tpt, _) if (
            name != nme.CONSTRUCTOR && !(sym is Synthetic) &&
            (sym is Accessor) && (sym is Lazy)
          ) => Some((sym, tpt.tpe, tree.rhs))

          case _ => None
        }
      }
    }

    object ExMutableFieldDef {
      def unapply(tree: tpd.ValDef): Option[(Symbol, Type, tpd.Tree)] = {
        val sym = tree.symbol
        tree match {
          case ValDef(_, tpt, _) if (
            !(sym is CaseAccessor) && !(sym is ParamAccessor) &&
            !(sym is Lazy) && !(sym is Synthetic) && !(sym is Accessor) && (sym is Mutable)
          ) => Some((sym, tpt.tpe, tree.rhs))

          case _ => None
        }
      }
    }

    object ExRequire {
      def unapply(tree: tpd.Apply): Option[tpd.Tree] = tree match {
        case Apply(ExSymbol("scala", "Predef$", "require"), Seq(body)) => Some(body)
        case _ => None
      }
    }

    object ExAssert {
      def unapply(tree: tpd.Apply): Option[(tpd.Tree, Option[String])] = tree match {
        case Apply(ExSymbol("scala", "Predef$", "assert"), Seq(body)) =>
          Some((body, None))
        case Apply(ExSymbol("scala", "Predef$", "assert"), Seq(body, Literal(cnst: Constant))) =>
          Some((body, Some(cnst.stringValue)))
        case _ => None
      }
    }

    object ExEnsuring {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case ExCall(Some(rec),
          ExSymbol("scala", "Predef$", "Ensuring", "ensuring") |
          ExSymbol("stainless", "lang", "StaticChecks$", "Ensuring", "ensuring"),
          _, Seq(contract)
        ) => Some((rec, contract))
        case _ => None
      }
    }

    object ExHolds {
      def unapplySeq(tree: tpd.Tree): Option[Seq[tpd.Tree]] = tree match {
        case ExCall(Some(rec),
          ExSymbol("stainless", "lang", "package$", "BooleanDecorations", "holds"),
          Seq(), args) => Some(rec +: args)
        case _ => None
      }
    }

    object ExBecause {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case ExCall(Some(rec),
          ExSymbol("stainless", "proof", "package$", "boolean2ProofOps", "because"),
          Seq(), Seq(proof)) => Some((rec, proof))
        case _ => None
      }
    }

    object ExComputes {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, tpd.Tree)] = tree match {
        case ExCall(Some(rec),
          ExSymbol("stainless", "lang", "package$", "SpecsDecorations", "computes"),
          _, Seq(expected)) => Some((rec, expected))
        case _ => None
      }
    }

    object ExWhile {
      def unapply(tree: tpd.Tree): Option[(tpd.Tree, Seq[tpd.Tree])] = tree match {
        case dd @ DefDef(nme.WHILE_PREFIX, Seq(), Seq(), unit, _) => dd.rhs match {
          case If(cond, Block(body, Apply(caller, Nil)), ExUnitLiteral()) if dd.symbol == caller.symbol => Some((cond, body))
          case _ => None
        }
        case _ => None
      }
    }
  }

}
