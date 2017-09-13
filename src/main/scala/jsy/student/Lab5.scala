package jsy.student

import jsy.lab5.Lab5Like

object Lab5 extends jsy.util.JsyApplication with Lab5Like {
  import jsy.lab5.ast._
  import jsy.util.DoWith
  import jsy.util.DoWith._

  /*
   * CSCI 3155: Lab 5
   * <D'Artagnan Wake>
   *
   * Partner: <Juan Vargas-Murillo>
   * Collaborators: <TA's and LA's>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   *
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */

  /*** Exercise with DoWith ***/

  def rename[W](env: Map[String,String], e: Expr)(fresh: String => DoWith[W,String]): DoWith[W,Expr] = {
    def ren(env: Map[String,String], e: Expr): DoWith[W,Expr] = e match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => doreturn(e)
      case Print(e1) => ren(env,e1) map { e1p => Print(e1p) }

      case Unary(uop, e1) => ren(env, e1) map {e1p => Unary(uop, e1p)}
      case Binary(bop, e1, e2) =>
        ren(env, e1) flatMap  { e1p =>
          ren(env, e2) map { e2p =>
            Binary(bop, e1p, e2p)
          }
        }
      case If(e1, e2, e3) => ren(env, e1) flatMap { e1p => ren(env, e2) flatMap { e2p => ren(env, e3) map { e3p => If(e1p, e2p, e3p) } } }

      case Var(x) => doreturn(Var(env.getOrElse(x,x)))

      case Decl(m, x, e1, e2) => fresh(x) flatMap { xp =>
        val envex = extend(env, x, xp)
        ren(env, e1) flatMap {
          e1p => ren(envex, e2) map {
            e2p => Decl(m, xp, e1p, e2p)
          }
        }
      }

      case Function(p, params, retty, e1) => {
        val w: DoWith[W,(Option[String], Map[String,String])] = p match {
          case None => doreturn((None, env))
          case Some(x) => fresh(x) map {xp => (Some(xp), extend(env, x, xp))}
        }
        w flatMap { case (pp, envp) =>
          params.foldRight[DoWith[W,(List[(String,MTyp)],Map[String,String])]]( doreturn((Nil, envp)) ) {
            case ((x,mty), acc) => acc flatMap {
              accp => {
                fresh(x) map { xp => ((xp, mty) :: accp._1, extend(accp._2, x, xp))}
              }
            }
          } flatMap {
            accp => ren(accp._2, e1) map { e1p => Function(pp, accp._1, retty, e1p)}
          }
        }
      }

      case Call(e1, args) => ren(env, e1) flatMap {
        e1p => mapWith(args) {
          arg => ren(env, arg)
        } map {
          argsp => Call(e1p, argsp)
        }
      }

      case Obj(fields) => mapWith(fields) { case (f,e) => ren(env, e) map {ep => (f, ep) } } map { e2p => Obj(e2p)}
      case GetField(e1, f) => ren(env, e1) map { e1p => GetField(e1p, f) }

      case Assign(e1, e2) => ren(env, e1) flatMap { e1p => ren(env, e2) map {e2p => Assign(e1p, e2p) }}

      /* Should not match: should have been removed */
      case InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
    ren(env, e)
  }

  def myuniquify(e: Expr): Expr = {
    val fresh: String => DoWith[Int,String] = { _ =>
      doget flatMap { i =>
        doput(i + 1) map (_ => "x" + i)
      }
      /*doget[Int] flatMap {
        (i) =>
          val xp = "x" + 1
          doput(i + 1) map { _ => xp}
      }*/
    }
    val (_, r) = rename(empty, e)(fresh)(0)
    r
  }

  /*** Helper: mapFirst to DoWith ***/

  // List map with an operator returning a DoWith
  def mapWith[W,A,B](l: List[A])(f: A => DoWith[W,B]): DoWith[W,List[B]] = {
    l.foldRight[DoWith[W,List[B]]]( doreturn(Nil) ) {
      (e, acc) => acc flatMap { accb => f(e) map {eb => eb::accb}}
      //(a, acc) => f(a) flatMap { ap => acc map { accp => ap :: accp}}
    }
  }

  // Map map with an operator returning a DoWith
  def mapWith[W,A,B,C,D](m: Map[A,B])(f: ((A,B)) => DoWith[W,(C,D)]): DoWith[W,Map[C,D]] = {
    m.foldRight[DoWith[W,Map[C,D]]]( doreturn(Map.empty) ) {
      (e, acc) => acc flatMap { accb => f(e) map {eb => accb + eb}}
      //(cd, acc) => f(cd) flatMap { cdp => acc map {accp => accp.updated(cdp._1, cdp._2)}}
      //(a, dw) =>
      //f(a).flatMap((r:B) => dw.map(r :: _))
      //f(a).flatMap((r: (C,D)) => dw.map((b:Map[C,D]) => b.))
    }
  }

  // Just like mapFirst from Lab 4 but uses a callback f that returns a DoWith in the Some case.
  def mapFirstWith[W,A](l: List[A])(f: A => Option[DoWith[W,A]]): DoWith[W,List[A]] = l match {
    case Nil => doreturn( Nil )//doreturn(l)
    case h :: t => f(h) match{
      case None => mapFirstWith(t)(f) map  {tp => h :: tp}//((newList: List[A]) => (h::newList)) //if h returns None, then we need to continue to cycle through mapFirstWith
      //until we do find a value that satisfies f
      case Some(withhp) =>  withhp map  {hp => hp :: t}//((newValueMapped: A) => (newValueMapped::t)) //This is when we find an element that satisfies f, we use the map
      //function since it is a DoWith function and mapFirstWith expects a DoWith returned.  This will map the new value returned from f into the list
      //and stop there, as well as returning W since we did not change anything to W, and that is our input-output state
    }
  }

  // There are better ways to deal with the combination of data structures like List, Map, and
  // DoWith, but we won't tackle that in this assignment.

  /*** Casting ***/

  def castOk(t1: Typ, t2: Typ): Boolean = (t1, t2) match {
      /***** Make sure to replace the case _ => ???. */
    case (t1, t2) if t1 == t2 => true
    case (TNull, TObj(_)) => true
    case (TObj(fields1), TObj(fields2)) =>
      (fields2 forall {case (f2, t2) => fields1.get(f2) match {case Some(t1) => t1==t2 case None => false}})||
        (fields1 forall {case (f1, t1) => fields2.get(f1) match {case Some(t2) => t1==t2 case None => false}})
      /***** Cases for the extra credit. Do not attempt until the rest of the assignment is complete. */
    case (TInterface(tvar, t1p), _) => ???
    case (_, TInterface(tvar, t2p)) => ???
      /***** Otherwise, false. */
    case _ => false
  }

  /*** Type Inference ***/

  // A helper function to check whether a jsy type has a function type in it.
  // While this is completely given, this function is worth studying to see
  // how library functions are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }

  def isBindex(m: Mode, e: Expr): Boolean = m match {
    case MConst | MName | MVar => true
    case MRef if isLExpr(e) => true
    case _ => true
  }

  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typeof(env, e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) if env.contains(x) => lookup(env, x) match { case MTyp(_, t) => t} //typeof(env, x).t
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
        /***** Cases directly from Lab 4. We will minimize the test of these cases in Lab 5. */
      case Unary(Not, e1) => typeof(env, e1) match{
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      //case Binary(Seq, e1, e2) => typeof(env, e1); typeof(env, e2)
      case Binary(Plus, e1, e2) => typeof(env, e1) match{
        case TNumber => typeof(env, e2) match{
          case TNumber => TNumber
          case tgot => err(tgot, e2)
        }
        case TString => typeof(env, e2) match{
          case TString => TString
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
        /*
        (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TString, TString) => TString
        case (tgot1, tgot2) => err(tgot1, e1); err(tgot2, e2)
        */
      }
      case Binary(Minus|Times|Div, e1, e2) => (typeof(env, e1), typeof(env, e2)) match{
        case (TNumber, TNumber) => TNumber
        case (TNumber, tgot) => err(tgot, e2)
        case (tgot, _) => err(tgot, e1)
        //case (tgot1, tgot2) => err(tgot1, e1); err(tgot2, e2)
      }
      case Binary(Eq|Ne, e1, e2) => typeof(env, e1) match {
        case t1 if !hasFunctionTyp(t1) => typeof(env, e2) match {
          case t2 if t1 == t2 => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => typeof(env, e1) match{
        case TNumber => typeof(env, e2) match{
          case TNumber => TBool
          case tgot => err(tgot, e2)
        }
        case TString => typeof(env, e2) match{
          case TString => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
        /*
        (typeof(env, e1), typeof(env, e2)) match{
        case (TNumber, TNumber) | (TString, TString) => TBool
        case (tgot1, tgot2) => err(tgot1, e1); err(tgot2, e2)
        */
      }
      case Binary(And|Or, e1, e2) => typeof(env, e1) match{
        case TBool => typeof(env, e2) match{
          case TBool => TBool
          case tgot => err(tgot, e2)
        }
        case tgot => err(tgot, e1)
        /*
        (typeof(env, e1), typeof(env, e2)) match {
        case (TBool, TBool) => TBool
        case (tgot1, tgot2) => err(tgot1, e1); err(tgot2, e2)
        */
      }
      case Binary(Seq, e1, e2) => {
        typeof(env, e1); typeof(env, e2)
        typeof(env, e1)
        typeof(env, e2)
      }
      case If(e1, e2, e3) => typeof(env, e1) match{
        case TBool => {
          if (typeof(env, e2) == typeof(env, e3)) typeof(env, e2) else err(typeof(env, e3), e3)
        }
        case tgot => err(tgot, e1)
      }

      case Obj(fields) => {
        TObj(fields.mapValues((e1)=> typeof(env, e1)))
      }
      case GetField(e1, f) => typeof(env, e1) match{
        //case TObj(field) if field.contains(f) => {
          //field(f)
        //}
        case TObj(fields) => fields(f)
        case tgot => err(tgot, e1)
      }


        /***** Cases from Lab 4 that need a small amount of adapting. */
      case Decl(m, x, e1, e2) if isBindex(m, e1) =>
        typeof(extend(env, x, MTyp(m, typeof(env, e1))), e2)
      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(tret)) =>
            val tprime = TFunction(params, tret)
            extend(env, f, MTyp(MConst, tprime))
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = params.foldLeft(env1) {
          (acc, e) => extend(acc, e._1, e._2)
          //case (envacc, (xi, mt)) =>
            //extend(envacc, xi, mt)
        }
        val t1 = typeof(env2, e1)
        // Match on whether the return type is specified.
        tann match {
          case None => TFunction(params, t1)
          case Some(tret) if tret == t1 => TFunction(params, t1)
          case _ => err(t1, e1)
        }
      }
      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params, args).zipped.foreach {
            case ((_ : String, MTyp(m : Mode, ti : Typ)), expr : Expr) => if (typeof(env, expr) != ti | !isBindex(m, expr)) {
              err(typeof(env, expr), expr)
            }
          }
          tret
        case tgot => err(tgot, e1)
      }

        /***** New cases for Lab 5. ***/
      case Assign(Var(x), e1) if lookup(env, x).m == MVar || lookup(env, x).m == MRef => typeof(env, e1) match {
        case t if t == lookup(env, x).t => t
        case tgot => err(tgot, e1)
      }
      //case Assign(Var(x), e1) =>
        //lookup(env, x) match {
          //case MTyp(m, t) if List(MVar, MRef).contains(m) & t == typeof(env, e1) => t
          //case _ => err(typeof(env, e1), e1)
        //}
      case Assign(GetField(e1, f), e2) => typeof(env, e1) match{
        case TObj(fields) if fields(f)==typeof(env, e2) => typeof(env, e2)
      }
      //case Assign(GetField(e1, f), e2) =>
        //e1 match {
          //case Obj(_) if typeof(env, e1) == typeof(env, e2) => typeof(env, e2)
          //case _ => err(typeof(env, e1), e1)
        //}
      case Assign(_, _) => err(TUndefined, e)

      case Null => TNull

      case Unary(Cast(t), e1) => typeof(env, e1) match {
        case tgot if castOk(tgot, t) => t
        case tgot => err(tgot, e1)
      }

      /* Should not match: non-source expressions or should have been removed */
      case A(_) | Unary(Deref, _) | InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
  }

  /*** Small-Step Interpreter ***/

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3 and Lab 4.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"inequalityVal: v1 ${v1} is not a value")
    require(isValue(v2), s"inequalityVal: v2 ${v2} is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => (bop: @unchecked) match{
        case Lt => s1 < s2
        case Le => s1 <= s2
        case Gt => s1 > s2
        case Ge => s1 >= s2
      }

      case (N(n1), N(n2)) => (bop: @unchecked) match{
        case Lt => n1 < n2
        case Le => n1 <= n2
        case Gt => n1 > n2
        case Ge => n1 >= n2
      }
    }
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => e
      case Print(e1) => Print(subst(e1))
        /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, substitute(e1, esub, x))
      case Binary(bop, e1, e2) => Binary(bop, substitute(e1, esub, x), substitute(e2, esub, x))
      case If(e1, e2, e3) => If(substitute(e1, esub, x), substitute(e2, esub, x), substitute(e3, esub, x))
      case Var(y) => if (y == x) esub else e
        /***** Cases need a small adaption from Lab 3 */
      case Decl(mut, y, e1, e2) => Decl(mut, y, subst(e1), if (x == y) e2 else subst(e2))
        /***** Cases needing adapting from Lab 4 */
      case Function(p, paramse, retty, e1) => p match {
        case None => if(paramse.exists(y => y._1==x)) e else Function(p, paramse, retty, substitute(e1, esub, x))
        case Some(y) => if(x==y || paramse.exists(y => y._1==x)) e else Function(p, paramse, retty, substitute(e1, esub, x))
      }
      //case Function(p, paramse, retty, e1) =>
        //(p, paramse) match {
          //case (Some(y), par) => if (y == x || paramse.exists(tup => tup._1 == x)) Function(p, paramse, retty, e1) else Function(p, paramse, retty, subst(e1))
          //case (None, par) => if(paramse.exists(tup => tup._1 == x)) Function(p, paramse, retty, e1) else Function(p, paramse, retty, subst(e1))
        //}
        /***** Cases directly from Lab 4 */
      case Call(e1, args) => Call(substitute(e1, esub, x), args.map(e => substitute(e, esub, x)))//Call(subst(e1), args map subst)
      case Obj(fields) => Obj(fields.mapValues(e => substitute(e, esub, x)))//Obj(fields map { case (fi,ei) => (fi, subst(ei)) })
      case GetField(e1, f) => if (x != f) GetField(substitute(e1, esub, x), f) else e
        /***** New case for Lab 5 */
      case Assign(e1, e2) => Assign(substitute(e1, esub, x), substitute(e2, esub, x))

      /* Should not match: should have been removed */
      case InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }

    def myrename(e: Expr): Expr = {
      val fvs = freeVars(esub)
      def fresh(x: String): String = if (fvs contains x) fresh(x + "$") else x
      rename[Unit](e)(doreturn(Null)){ x => doreturn(fresh(x)) }
    }

    subst(myrename(e))
  }

  /* Check whether or not an expression is reduced enough to be applied given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match{
    case MConst| MVar if !isValue(e) => true
    case MRef if !isLValue(e) => true
    case _ => false
    // /case MConst => if (isValue(e)) false else true
    //case MName => false
  }

  def getBinding(mode: Mode, e: Expr): DoWith[Mem,Expr] = {
    require(!isRedex(mode,e), s"expression ${e} must not reducible under mode ${mode}")
    mode match {
      case MConst|MName => doreturn(e)
      case MVar => memalloc(e) map { A => Unary(Deref, A)}
      case MRef if isLValue(e) => doreturn(e)
    }
  }

  /* A small-step transition. */
  def step(e: Expr): DoWith[Mem, Expr] = {
    require(!isValue(e), "stepping on a value: %s".format(e))
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => doget map { m => println(pretty(m, v1)); Undefined }
        /***** Cases needing adapting from Lab 3. */
      //case Unary(Neg, v1) if isValue(v1) => ???
      case Unary(Neg, N(n)) => doget map {_ => N(-n)}
      case Unary(Not, B(b)) => doget map {_ => B(!b)}
      case Unary(Cast(t), v1) if isValue(v1) => v1 match {
        case Null => t match {
          case TObj(_)|TInterface(_,_) => doget map {_ => v1}
          case _ => throw StuckError(e)
        }
        case a@A(_) => doget map {mem =>
          mem.get(a) match {
            case Some(Obj(fields1)) => t match {
              case TObj(fields2) if fields2 forall {case (f2, t2) => fields1.contains(f2)} =>  v1
              case TInterface(x, t) if fields1.contains(x) => v1
              case _ => throw DynamicTypeError(v1)
            }
            case None => throw StuckError(e)
          }
        }
        case _ => doget map {_ => v1}
      }
      case Binary(Seq, v1, e2) if isValue(v1) => doget map {_ => e2}
      case Binary(Plus, v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match {
        case (N(n1), N(n2)) => doget map {_ => N(n1+n2)}
        case (S(s1), S(s2)) => doget map {_ => S(s1+s2)}
        case (_, _) => throw StuckError(e)
      }
      case Binary(bop@(Minus|Times|Div), N(n1), N(n2)) => bop match {
        case Minus => doget map {_ => N(n1-n2)}
        case Times => doget map {_ => N(n1*n2)}
        case Div => doget map {_ => N(n1/n2)}
        case _ => throw StuckError(e)
      }
      case Binary(bop@(Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => (v1, v2) match{
        case (N(_), N(_)) | (S(_), S(_)) => doget map {_ => B(inequalityVal(bop, v1, v2))}
        case (_, _) => throw StuckError(e)
      }
      case Binary(bop@(Eq|Ne), v1, v2) if isValue(v1) && isValue(v2) => bop match {
        case Eq => doget map {_=> B(v1 == v2)}
        case Ne => doget map {_=> B(v1 != v2)}
        case _ => throw StuckError(e)
      }
      case Binary(And, e1, e2) if isValue(e1) => e1 match {
        case B(true) => doget map {_=> e2}
        case B(false) => doget map {_=> e1}
        case _ => throw StuckError(e)
      }
      case Binary(Or, e1, e2) if isValue(e1) => e1 match {
        case B(true) => doget map {_=> e1}
        case B(false) => doget map {_=> e2}
        case _ => throw StuckError(e)
      }
      case If(e1, e2, e3) if isValue(e1) => e1 match {
        case B(true) => doget map {_=> e2}
        case B(false) => doget map {_=> e3}
        case _ => throw StuckError(e)
      }
        /***** More cases here */
        /***** Cases needing adapting from Lab 4. */
      case Obj(fields) if (fields forall { case (_, vi) => isValue(vi)}) => memalloc(Obj(fields))
        //memalloc(e) flatMap {
          //a => domodify[Mem] {
            //m => m.+(a, e)
          //} flatMap {
            //_ => doreturn(a)
          //}
        //}
      case GetField(a @ A(_), f) => doget map {mem => mem.get(a) match {
        case Some(Obj(fields)) if fields.contains(f) => fields(f)
        case _ => throw StuckError(e)
        }
      }
      //case GetField(a @ A(_), f) =>
        //doget map {
          //m => m.get(a) match {
            //case Some(Obj(fields)) => fields.get(f) match {
              //case Some(v) => v
              //case _ => throw NullDereferenceError(e)
            //}
            //case _ => throw NullDereferenceError(e)
          //}
        //}

      case Decl(MConst, x, v1, e2) if isValue(v1) && isBindex(MConst, v1) => getBinding(MConst, v1) map {e1p => substitute(e2, e1p, x)}
      case Decl(MVar, x, v1, e2) if isValue(v1) && isBindex(MName, v1) => getBinding(MVar, v1) map {e1p => substitute(e2, e1p, x)}

      //case Decl(MConst, x, v1, e2) if isValue(v1) =>
        //getBinding(MConst, v1) flatMap {
          //v1p => doreturn(substitute(e2, v1p, x))
        //}
      //case Decl(MVar, x, v1, e2) if isValue(v1) =>
        //getBinding(MVar, v1) flatMap {
          //v1p => doreturn(substitute(e2, v1p, x))
        //}

        /***** New cases for Lab 5. */
      case Unary(Deref, a @ A(_)) =>
        doget map {
          m => m.get(a) match {
            case Some(e) => e
            case _ => throw StuckError(e)
          }
        }

      case Assign(Unary(Deref, a @ A(_)), v) if isValue(v) =>
        domodify[Mem] { m => m.+(a -> v) } map { _ => v }

      case Assign(GetField(a @ A(_), f), v) if isValue(v) =>
        domodify[Mem] {
          m => m.get(a) match {
            case Some(Obj(fields)) => m.+(a, Obj(fields.updated(f, v)))
            case _ => throw StuckError(e)
          }
        } map {
          _ => v
        }

      case Call(v @ Function(p, params, _, e), args) => {
        val pazip = params zip args
        if (pazip.forall(e => !isRedex(e._1._2.m, e._2))) {
          val dwep = pazip.foldRight( doreturn(e) : DoWith[Mem,Expr] )  {
            case (((xi, MTyp(mi, _)), ei), dwacc) => dwacc flatMap  {acc => getBinding(mi, ei) map {eib => substitute(acc, eib, xi)}}
          }
          p match {
            case None => dwep
            case Some(x) => dwep map {d => substitute(d, v, x)}
          }
        }
        else {
          val dwpazipp = mapFirstWith(pazip) {
            p => if(isRedex(p._1._2.m, p._2)) Some(step(p._2) map {p2s => (p._1, p2s)}) else None
          }
          dwpazipp map {e => Call(v, e.map(i => i._2))}
        }
      }
      /* Base Cases: Error Rules */
        /***** Replace the following case with a case to throw NullDeferenceError.  */
      case GetField(Null, f) => throw NullDereferenceError(GetField(Null, f))
      case Assign(GetField(Null, f), v) => throw NullDereferenceError(Assign(GetField(Null, f), v))

      /* Inductive Cases: Search Rules */
        /***** Cases needing adapting from Lab 3. Make sure to replace the case _ => ???. */
      //case Print(e1) => step(e1) map { e1p => Print(e1p) }
      //case Unary(uop, e1) if !isValue(e1) => step(e1) map {ep => Unary(uop, ep)}
      case Print(e1) => step(e1) map { e1p => Print(e1p) }
      case Unary(uop, e1) => step(e1) map {e1s => Unary(uop, e1s)}
      case Binary(bop, v1, e2) if isValue(v1) => step(e2) map {e2s => Binary(bop, v1, e2s)}
      case Binary(bop, e1, e2) => step(e1) map {e1s => Binary(bop, e1s, e2)}
      case If(e1, e2, e3) => step(e1) map {e1s => If(e1s, e2, e3)}
        /***** Cases needing adapting from Lab 4 */
      case GetField(e1, f) => step(e1) map {e1s => GetField(e1s, f)}
      case Obj(fields) => mapWith(fields)({f: ((String, Expr)) => step(f._2) map {es => (f._1, es)}}) map {fieldss => Obj(fieldss)}

      case Decl(mode, x, e1, e2) if isRedex(mode, e1) => step(e1) map {e1s => Decl(mode, x, e1s, e2)}
      case Call(e1, args) => step(e1) map {e1s => Call(e1s, args)}

      //case GetField(e1, f) =>
        //step(e1) map {
          //ep => GetField(ep, f)
        //}
      //case Obj(fields) =>
        //mapWith(fields) {
          //case (s, ex) if !isValue(ex) => step(ex) map {
            //ep => (s, ep)
          //}
          //case f => doreturn[Mem, (String, Expr)](f)
        //} map {
          //fieldsp => Obj(fieldsp)
        //}

      //case Decl(mode, x, e1, e2) =>
        //step(e1) map {
          //e1p => Decl(mode, x, e1p, e2)
        //}
      //case Call(e1, args) =>
        //step(e1) map {
          //e1p => Call(e1p, args)
        //}

        /***** New cases for Lab 5.  */
      case Assign(e1, e2) if !isLValue(e1) => step(e1) map {e1s => Assign(e1s, e2)}
      case Assign(e1, e2) => step(e2) map {e2s => Assign(e1, e2s)}
      //case Assign(e1, e2) if !isLValue(e1) & !isValue(e1) =>
        //step(e1) map {
          //ep => Assign(ep, e2)
        //}
      //case Assign(e1, e2) if !isValue(e2) & isLValue(e1)=>
        //step(e2) map {
          //ep => Assign(e1, ep)
        //}

      /* Everything else is a stuck error. */
      case _ => throw StuckError(e)
    }
  }

  /*** Extra Credit: Lowering: Remove Interface Declarations ***/

  def lower(e: Expr): Expr =
    /* Do nothing by default. Change to attempt extra credit. */
    e

  /*** External Interfaces ***/

  //this.debug = true // comment this out or set to false if you don't want print debugging information
  this.maxSteps = Some(1000) // comment this out or set to None to not bound the number of steps.
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}
