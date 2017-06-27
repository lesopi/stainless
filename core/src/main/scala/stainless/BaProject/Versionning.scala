/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package BAProject

object VersionningDebugSection extends inox.DebugSection("versionning")

object Versionning extends Component {
  val name = "versionning"
  val description = "Verification of function contracts"

  val trees: extraction.xlang.trees.type = extraction.xlang.trees

  type Report = VersionNameReport
  type MyProgram = Program{val trees: extraction.xlang.trees.type}

  val lowering = inox.ast.SymbolTransformer(new ast.TreeTransformer {
    val s: extraction.trees.type = extraction.trees
    val t: extraction.trees.type = extraction.trees
  })

  implicit val debugSection = VersionningDebugSection

  import trees._

  trait VersionNameReport extends AbstractReport { self =>
    val program: MyProgram
    //val expr: Expr
    val transformer: Transformer
    import program._

    def emit(): Unit = {
      ctx.reporter.info(transformer)
    }
  }


  sealed abstract class Transformer;

  // Expression transformers
  sealed abstract class ExprTransformer extends Transformer;
  case object NoOp extends ExprTransformer;
  case class Delete(e: Expr, p: List[Int]) extends ExprTransformer;
  case class Insert(e: Expr, p: List[Int]) extends ExprTransformer; // recall replace
  case class Substitute(e1: Expr, e2: Expr) extends ExprTransformer;
  case class Replace(e: Expr, p: List[Int]) extends ExprTransformer;
  case class ChangeExpr(e: Expr, p: List[Int]) extends ExprTransformer;
  case class ComposeExpr(t1: ExprTransformer, t2: ExprTransformer) extends ExprTransformer;

  case class Compose(t1: Transformer, t2: Transformer) extends Transformer;

  // functionTransformers
  sealed abstract class FunTransformer extends Transformer;
  case class DeleteFunction(fd: FunDef) extends FunTransformer;
  case class InsertFunction(fd: FunDef) extends FunTransformer;
  case class RenameFunction(src: FunDef, tg: FunDef) extends FunTransformer;
  case class ChangeArguments(src: FunDef, tg: FunDef) extends FunTransformer;
  case class ChangeReturnType(src: FunDef, tg: FunDef) extends FunTransformer;
  case class ChangeBody(f: FunDef, tr: ExprTransformer) extends FunTransformer;
  case object NoOperation extends FunTransformer;

  //classTransformers
  sealed abstract class ClassTransformer extends Transformer;
  case class DeleteClass(cd:ClassDef) extends ClassTransformer;
  case class InsertClass(cd: ClassDef) extends ClassTransformer;
  case class RenameClass(src: ClassDef, tg: ClassDef) extends ClassTransformer;
  case class ChangeMeth(c: ClassDef,
    m1: List[SymbolIdentifier],
    m2: List[SymbolIdentifier]) extends ClassTransformer;
  case class ChangeFields(c: ClassDef,
      pf1: Seq[ValDef],
      pf2: Seq[ValDef]) extends ClassTransformer;

  case object NoOpClass extends ClassTransformer;





  def apply(units: List[UnitDef], p: MyProgram): VersionNameReport = {
    import p._

    import p.symbols._

    // program functions to adapt input

    /*
    * Separates the program into two different programs, they are extracted
    * from the units given in apply. We assume that the two programs we
    * want to compare are given in two objects, so we take the first two units.
    */
    def separateUnits(): (MyProgram, MyProgram) = {
      val obj1 = units.head.modules(0)
      val prog1: MyProgram = new inox.Program {
        val trees: p.trees.type = p.trees
        val ctx = p.ctx
        val symbols = trees.Symbols(p.symbols.functions.values.filter(f => obj1.functions.contains(f.id))
        .map(fd => fd.id -> fd).toMap,
        p.symbols.adts,
        p.symbols.classes.values.filter(c => obj1.classes.contains(c.id))
        .map(cd => cd.id -> cd).toMap)
      }

      val obj2 = units.head.modules(1)
      val prog2: MyProgram = new inox.Program {
        val trees: p.trees.type = p.trees
        val ctx = p.ctx
        val symbols = new trees.Symbols(
          p.symbols.functions.values.filter(f => obj2.functions.contains(f.id))
          .map(fd => fd.id -> fd).toMap,
          p.symbols.adts,
          p.symbols.classes.values.filter(c => obj2.classes.contains(c.id))
          .map(cd => cd.id -> cd).toMap)
        }

        (prog1, prog2)
    }

    /*
    * Takes two programs and normalizes them so that every ids are the same if
    * they correspond to values with same name and same types.
    */
    def normalizePrograms(p1: MyProgram, p2: MyProgram): (MyProgram, MyProgram) = {

      // a class is defined by its name
      var classMap = collection.immutable.Map[String, Identifier]()

      // a value is defined by its name and its type
      var valMap = collection.immutable.Map[(String, Type), ValDef]()

      // a function is defined by its name, the type of its arguments
      // and its return type
      var funMap = collection.immutable.Map[(String, Seq[Type], Type), Identifier]()

      // a type parameter is defined by its name
      var typeParamMap = collection.immutable.Map[String, Identifier]()

      object pTrans extends SelfTreeTransformer {
        override def transform(vd: ValDef): ValDef = {
          val newTpe = transform(vd.tpe)
          val tup = (vd.id.name, newTpe)
          valMap.get(tup) match{
            case Some(v) => {
              v
            }
            case None => {
              valMap = valMap + (tup -> vd)
              vd
            }
          }
        }

        override def transform(t: Type): Type = t match {
          case ct @ ClassType(id, tps) => {
            val newId = classMap.get(id.name) match{
              case Some(clId) => clId
              case None =>{
                classMap = classMap + (id.name -> id)
                id
              }
            }
            //super.transform(ct.copy(id = newId))
            ct
          }
          case tp: TypeParameter => {
            val newTypeId = typeParamMap.get(tp.id.name) match{
              case Some(tpId) => tpId
              case None => {
                typeParamMap = typeParamMap + (tp.id.name -> tp.id)
                tp.id
              }
            }
            super.transform(tp.copy(id = newTypeId))

          }
          // dans le cas d'une classe ou d'un parametre de type (ex A)
          case _ => super.transform(t)

        }
        override def transform(e: Expr): Expr = e match{
          /*
          * in the case of a function invocation, you have to normalize
          * the parameter types if there are any; and then the id of the
          * function
          */
          case fi @ FunctionInvocation(id, tps, args) => {
            val newTps = tps.map(transform(_))
            val newId = funMap.get((id.name, args.map(_.getType), fi.getType)) match{
              case Some(funId) => funId
              case None => {
                funMap = funMap + ((id.name, args.map(_.getType), fi.getType) -> id)
                id
              }
            }
            super.transform(fi.copy(id = newId, tps = newTps))
          }
          case _ => super.transform(e)
        }
      }

      def getNewProgram(tr: MyProgram): MyProgram = {
        val newFunct = tr.symbols.functions.values.toSeq.map(fd =>
          fd.copy(
            id = funMap.get(fd.id.name, fd.params.map(_.tpe), fd.returnType) match{
              case Some(funId) => funId
              case None => {
                funMap = funMap + ((fd.id.name, fd.params.map(_.tpe), fd.returnType) -> fd.id)
                fd.id
              }
            })
          )

          val newClasses = tr.symbols.classes.values.toSeq.map(cd =>
            cd.copy(
              id = classMap.get(cd.id.name) match {
                case Some(cid) => cid
                case None => {
                  classMap = classMap + (cd.id.name -> cd.id)
                  cd.id
                }
              })
            )


            new inox.Program {
              val trees: tr.trees.type = tr.trees
              val ctx = tr.ctx
              val symbols = NoSymbols
              .withFunctions(newFunct)
              .withClasses(newClasses)
            }
      }

      (getNewProgram(p1.transform(pTrans)), getNewProgram(p2.transform(pTrans)))
    }

    // expression functions

    /*
    * Finds what if the transformer that corresponds to
    * the transformation between the two expressions
    */
    def compare(e1: Expr, e2: Expr): ExprTransformer = {

      def composition(l: List[ExprTransformer]): ExprTransformer = {
        if (l.size == 0) NoOp
        else if (l.size == 1) l.head
        else ComposeExpr(l.head, composition(l.tail))
      }

      def findTransformer(ex1: Expr, ex2: Expr, path: List[Int] = Nil): ExprTransformer = {
        val Operator(c1, f1) = ex1
        val Operator(c2, f2) = ex2

        if(ex1 == ex2 || ex1.toString == ex2.toString) NoOp
        else {
          (ex1, ex2) match{
            case (FunctionInvocation(id1, tp1, ag1), FunctionInvocation(id2, tp2, ag2)) if(id1.name != id2.name) =>{
              ChangeExpr(ex2, path)
            }
            case _ if(ex1.getClass != ex2.getClass) =>
            if(c1 == c2) ChangeExpr(ex2, path)  else Substitute(ex1, ex2)
            case _ => {
              val zp = c1.zipAll(c2, null, null)
              var trf : List[ExprTransformer] = Nil

              if(zp.isEmpty) {
                path match {
                  case Nil => Substitute(ex1, ex2)
                  case _ => Replace(ex2, path)
                }
              } else {
                for((ch1, ch2) <- zp){
                  if(ch1 != ch2) {
                    if(ch1 == null) trf = Insert(ch2, path ++ List(c2.indexOf(ch2))) :: trf
                    else if(ch2 == null) trf = Delete(ch1, path ++ List(c1.indexOf(ch1))) :: trf
                    else (ch1, ch2) match {
                        case (FunctionInvocation(id1, tp1, ag1), FunctionInvocation(id2, tp2, ag2)) =>{
                          ChangeExpr(ch2, path ++ List(c1.indexOf(ch1)))
                        }
                        case _  if (ch1.getClass == ch2.getClass)=> trf = findTransformer(ch1, ch2, path ++ List(c1.indexOf(ch1))) :: trf
                        case _ =>  {
                          val Operator(chh1, ff1) = ch1
                          val Operator(chh2, ff2) = ch2
                          if (chh1 == chh2)
                            trf = ChangeExpr(ch2, path ++ List(c1.indexOf(ch1))) :: trf
                          else{

                            trf = Replace(ch2, path ++ List(c1.indexOf(ch1))) :: trf}
                        }
                      }

                  }
                }
                composition(trf)
              }
            }
          }
        }
      }
      findTransformer(e1, e2, Nil)
    }

    /*
    * Finds the result expression when applying a transformer to an expression
    */
    def eval(e: Expr, trf: ExprTransformer): Expr = {
      val Operator(es, f) = e
      trf match {
        case NoOp => e

        case Insert(ins_ex, p) => p match{
          case Nil => e
          case x :: Nil => {
            val newChildren = es.patch(x, Seq(ins_ex), 0)
            f(newChildren)
          }
          case x :: xs => {
            val child = eval(es(x), Insert(ins_ex, xs))
            val newChildren = es.patch(x, Seq(child), 1)
            f(newChildren)
          }
        }

        case Delete(del_ex, p) => p match {
          case Nil => e
          case x :: Nil => {
            val newChildren = es.patch(x, Nil, 1)
            f(newChildren)
          }
          case x :: xs => {
            val child = eval(es(x), Delete(del_ex, xs))
            val newChildren = es.patch(x, Seq(child), 1)
            f(newChildren)
          }
        }

        case Substitute(orig, sub) => {
          if(e == orig) sub else  f(es.map(eval(_, trf)))
        }

        case ComposeExpr(t1, t2) => eval(eval(e, t1), t2)

        case Replace(rep_ex, p) => p match{
          case Nil => rep_ex // if there is no path replace the whole tree
          // no need to do the case x :: Nil because rep_ex replaces in case of Nil
          case x :: xs => {
            val child = eval(es(x), Replace(rep_ex, xs))
            val newChildren = es.patch(x, Seq(child), 1)
            f(newChildren)
          }
        }

        case ChangeExpr(e1, p) => eval(e, Replace(e1, p)) // that acts like an eval,
        // since e1 and base expression have same childrens but different fucntions.
        // this transformer is just for weight mesuring


        case _ => e
      }
    }

    // functions at program level
    // Helper functions
    /*
    * gives a weight to every transformer so that you can find
    * the "closest" transformation, i.e the couple that has been the less transformed
    */
    def getWeight(tr: Transformer, ex: Expr = null): Int = {
      val fsize = if (ex != null) exprOps.formulaSize(ex) else 0
      val w = tr match{
        case NoOp => 0
        case Delete(e, path) =>  fsize - (exprOps.formulaSize(e) + path.length)
        case Insert(e, path) =>  fsize - (exprOps.formulaSize(e) + path.length)
        case Substitute(e1, e2) => exprOps.formulaSize(e1) + exprOps.formulaSize(e2)
        case Replace(e, path) =>  fsize - (exprOps.formulaSize(e) + path.length)
        case ComposeExpr(t1, t2) => getWeight(t1, ex) + getWeight(t2, ex)
        case ChangeExpr(e, path) => fsize - (exprOps.formulaSize(e) + path.length)
        case NoOperation => 0
        case DeleteFunction(fd) => exprOps.formulaSize(fd.fullBody)
        case InsertFunction(fd) => exprOps.formulaSize(fd.fullBody)
        case RenameFunction(src, tg) => 5
        case ChangeArguments(src, tg) => 1
        case ChangeReturnType(src, tg) => 1
        case ChangeBody(f, trf) => getWeight(trf, f.fullBody)
        case Compose(t1, t2) => getWeight(t1) + getWeight(t2)
        case DeleteClass(c) => c.methods.size + c.fields.size
        case InsertClass(c) => c.methods.size + c.fields.size
        case RenameClass(c1, c2) => 5
        case ChangeMeth(c, m1, m2) => m1.zip(m2).count(meth => meth._1 != meth._2)
        case ChangeFields(c, pf1, pf2) => pf1.zip(pf2).count(fi => fi._1 != fi._2)
        case NoOpClass => 0
        case _ => Int.MaxValue
      }
      if(w < 0) 0 else w
    }

    /*
    * traverses both lists of elements and finds all possible couples
    */
    def getMapping[T](source: List[T], target: List[T]): List[List[(Option[T], Option[T])]] = {

      /*
      * get all possible permutations in a list
      */
      def prod[U](lst1: List[U], lst2: List[U]) = (List.fill(1)(lst2).flatMap(_.permutations)).map(lst1.zip(_)).toList

      // fill smallest list with None so that both list have the same size
      val diff = source.length - target.length
      val l1 = if(diff < 0)
      source.map(Some(_)) ::: List.fill(-diff)(None)
      else source.map(Some(_))

      val l2 = if(diff > 0)
      target.map(Some(_)) ::: List.fill(diff)(None)
      else target.map(Some(_))

      prod(l1, l2)
    }

    /*
    * keeps the best tansformer through a list of transformers
    */
    def getBest(trf: List[Transformer], best: Transformer, weight: Int = Int.MaxValue): Transformer = trf match{
      case Nil => best
      case x :: xs => {
        val w = getWeight(x)
        if(w < weight) getBest(xs, x, w) else getBest(xs, best, weight)
      }
    }

    /*
    * Combines all the transformers into a single one
    */
    def comp(tr: List[Transformer]): Transformer = {
      tr match{
        case Nil => NoOperation
        case t :: Nil => t
        case t :: ts => Compose(t, comp(ts))
      }
    }

    // Comparison functions
    /*
    * finds all transformations between two lists of functions
    */
    def funTransformations(source: List[FunDef], target: List[FunDef]): Transformer = {

      def signature(preFun: FunDef, postFun: FunDef): Boolean =
        preFun.id.name == postFun.id.name &&
        (preFun.params.zip(postFun.params).forall(pp => pp._1 == pp._2 || pp._1.toString == pp._2.toString))&&
        (preFun.returnType == postFun.returnType || preFun.returnType.toString == preFun.returnType.toString )

      def getSignatureTransformer(preFun: FunDef, postFun: FunDef): Transformer = {
        var trfs: List[Transformer] = Nil
        if(preFun.id.name != postFun.id.name) trfs = RenameFunction(preFun, postFun) :: trfs
        if(preFun.params != postFun.params) trfs = ChangeArguments(preFun, postFun) :: trfs
        if(preFun.returnType != postFun.returnType) trfs = ChangeReturnType(preFun, postFun) :: trfs
        comp(trfs)
      }

      /*
      * creates a transformer that represents the transformations
      * between all couples of funtions
      */
      def composition(mapping: List[(Option[FunDef], Option[FunDef])]): Transformer = mapping match{
        case Nil => NoOperation
        case _ => {
          // The list of transformers obtained from couples
          val transformersMapping =  mapping.map(tup => tup match{
            case (None, None) =>  NoOperation
            case (None, Some(postFun)) => InsertFunction(postFun)
            case (Some(preFun), None) => DeleteFunction(preFun)
            case (Some(preFun), Some(postFun))=> {val o = {

              if (signature(preFun, postFun) && preFun.fullBody == postFun.fullBody)
              NoOperation
              else if(signature(preFun, postFun))
              ChangeBody(preFun, compare(preFun.fullBody, postFun.fullBody))
              else if(preFun.fullBody == postFun.fullBody)
              getSignatureTransformer(preFun, postFun)
              else Compose(
                ChangeBody(preFun, compare(preFun.fullBody, postFun.fullBody)),
                getSignatureTransformer(preFun, postFun))
            }


          if(preFun.id.name == "fill" && (postFun.id.name == "fill" || postFun.id.name == "mkString")){
            //ctx.reporter.info(postFun.id.name)
            //ctx.reporter.info(o)
          }
          o
        }})
          comp(transformersMapping.filterNot(_ == NoOperation))
        }
      }
      getBest(getMapping(source, target).map(composition(_)), NoOp)
    }

    /*
    * finds the best transformation between two list of classes
    */
    def classTransformations(source: List[ClassDef], target: List[ClassDef]): Transformer={
      /*
      * creates a transformer that represents the transformations
      * between all couples of classes
      */
      def composition(mapping: List[(Option[ClassDef], Option[ClassDef])]): Transformer = mapping match{
        case Nil => NoOpClass
        case _ => {
          // The list of transformers obtained from couples
          val transformersMapping =  mapping.map(tup => tup match{
            case (None, None) =>  NoOpClass
            case (None, Some(postClass)) => InsertClass(postClass)
            case (Some(preClass), None) => DeleteClass(preClass)
            case (Some(preClass), Some(postClass))=> {
              var trfs: List[Transformer] = Nil
              if (preClass.id != postClass.id) trfs = RenameClass(preClass, postClass) :: trfs
              if (preClass.fields != postClass.fields)
                trfs = ChangeFields(postClass, preClass.fields, postClass.fields) :: trfs
              if (preClass.methods.map(_.name) != postClass.methods.map(_.name))
                trfs = ChangeMeth(postClass, preClass.methods.toList, postClass.methods.toList) :: trfs
              comp(trfs)
            }
          })
          comp(transformersMapping.filterNot(_ == NoOperation))
        }
      }

      getBest(getMapping(source, target).map(composition(_)), NoOperation)
    }

    def programTransformation(s: MyProgram, t: MyProgram): Transformer = {
      val classTrf = classTransformations(s.symbols.classes.values.toList,
        t.symbols.classes.values.toList)
      val funTrf = funTransformations(s.symbols.functions.values.toList,
        t.symbols.functions.values.toList)
      comp(List(classTrf, funTrf).filterNot(_ == NoOperation))
    }

    /*
    * usefull to display the transformer
    */
    def transformerToString(tr: Transformer): String = tr match{
      case DeleteClass(c) => "the class " + c.id.name + " was removed"
      case InsertClass(c) => "the class " + c.id.name + " was inserted"
      case RenameClass(c1, c2) => "the class " + c1.id.name + " was renamed into " +  c2.id.name
      case ChangeMeth(c, m1, m2) => "the functions of the class " + c.id.name + " were changed"
      case ChangeFields(c, pf1, pf2) => "the fields of the class " + c.id.name + " were changed"
      case DeleteFunction(fd) => "the function " + fd.id.name + " was deleted"
      case InsertFunction(fd) => "the function " + fd.id.name + " was inserted"
      case RenameFunction(sfd, tfd) => " the function " + sfd.id.name + " was renamed into " + tfd.id.name
      case ChangeArguments(sfd, tfd) => "the arguments of the function " + sfd.id.name + " were modified"
      case ChangeReturnType(sfd, tfd) => "the return type of the function " + sfd.id.name + " was modified into " + tfd.returnType
      case ChangeBody(fd, t) => "the body of the function " + fd.id.name + " was modified"
      case Compose(t1, t2) => transformerToString(t1) + "\n and then " + transformerToString(t2)
      case _ => ""
    }


    /******************************TESTING*************************************/
    // testing separateUnits funtion
    val (p1, p2) = separateUnits()
    //ctx.reporter.info(p1.symbols.functions.values)
    //ctx.reporter.info(p2.symbols.functions.values)


    // testing normalizePrograms function
    val (normP1, normP2) = normalizePrograms(p1, p2)

    val trf = programTransformation(normP1, normP2)

    ctx.reporter.info(transformerToString(trf))
    /**************************************************************************/



    new VersionNameReport {
      val transformer = trf

      //val expr = eval(fromfd.fullBody, Insert(testfd.fullBody, List(2)))
      val program = p
    }
  }
}
