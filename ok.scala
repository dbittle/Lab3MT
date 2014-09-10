object Lab3 extends jsy.util.JsyApplication {
  import jsy.lab3.ast._
  
  /*
   * CSCI 3155: Lab 3 
   * <Your Name>
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   * 
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * 'throws new UnsupportedOperationException' as needed to get something
   * that compiles without error.
   */
  
  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }
  
  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0
      case B(true) => 1
      case Undefined => Double.NaN
      case S(s) => try s.toDouble catch { case _: Throwable => Double.NaN }
      case Function(_, _, _) => Double.NaN
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) if (n compare 0.0) == 0 || (n compare -0.0) == 0 || n.isNaN => false
      case N(_) => true
      case B(b) => b
      case Undefined => false
      case S("") => false
      case S(_) => true
      case Function(_, _, _) => true
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => if (n.isWhole) "%.0f" format n else n.toString
      case B(b) => b.toString
      case Undefined => "undefined"
      case S(s) => s
      case Function(_, _, _) => "function"
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
	require(isValue(v1))
	require(isValue(v2))
	require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) =>
        (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
        }
      case _ =>
        val (n1, n2) = (toNumber(v1), toNumber(v2))
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */
  
  /*
   * This code is a reference implementation of JavaScripty without
   * strings and functions (i.e., Lab 2).  You are to welcome to
   * replace it with your code from Lab 2.
   */
  def eval(env: Env, e: Expr): Expr = {
    def eToN(e: Expr): Double = toNumber(eval(env, e))
    def eToB(e: Expr): Boolean = toBoolean(eval(env, e))
    def eToS(e: Expr): String = toStr(eval(env,e))
    def eToVal(e: Expr): Expr = eval(env, e)
    e match {
      /* Base Cases */
      case _ if isValue(e) => e
      case Var(x) => get(env, x)
      
      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined
      
      case Unary(uop,e1) => uop match {
        case Neg => N(-eToN(e1))
        case Not => B(!eToB(e1))
      }
      
      case Binary(bop,e1,e2) => {
        val rv1 = eToVal(e1)
        val rv2 = eToVal(e2)
        
        bop match {
          //Logical
          case Eq => B(isEqual(rv1,rv2))
          case Ne => B(!isEqual(rv1,rv2))
          case Lt | Le | Gt | Ge => B(inequalityVal(bop, eToVal(e1), eToVal(e2)))
          case And => if (toBoolean(rv1)) rv2 else rv1
          case Or => if (toBoolean(rv1)) rv1 else rv2
          
          //Arithmetic
          case Plus => (rv1,rv2) match {
            case (S(_),_) | (_,S(_)) => S(toStr(rv1)+toStr(rv2))
		    case (v1, v2) => N(toNumber(v1) + toNumber(v2))
          } case Minus => N(eToN(e1) - eToN(e2))
          case Times => N(eToN(e1) * eToN(e2))
          case Div => N(eToN(e1) / eToN(e2))
          
          case Seq => rv2
        }
      }
      
      case If(e1, e2, e3) => if (eToB(e1)) eToVal(e2) else eToVal(e3)
      
      case ConstDecl(x, e1, e2) => {
        e1 match {
          case Function(_,_,_) => eval(extend(env,x,e1),e2);
          case _ => eval(extend(env, x, eToVal(e1)), e2)
        }
      }
      
      case Call(e,e2) => eToVal(e) match {
        case Function(None,str,e1) => eval(extend(env,str,eToVal(e2)),e1);
        case Function(Some(fn),str,e1) => eval(extend(extend(env,fn,eToVal(e)),str,eToVal(e2)),e1)
        case _ => throw DynamicTypeError(e)
      }
      
      case _ => throw new UnsupportedOperationException
    }
  }
    

  /* Small-Step Interpreter with Static Scoping */
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    /* Simple helper that calls substitute on an expression
     * with the input value v and variable name x. */
    def subst(e: Expr): Expr = substitute(e, v, x)
    /* Body */
    e match {
      case Var(str) => if (str == x) v else e
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(subst(e1))
      case ConstDecl(jsv,e1,e2) => (e1,e2) match {
        case _ if (jsv == x) => ConstDecl(jsv,subst(e1),e2)
        case _ if (jsv != x) => ConstDecl(jsv,subst(e1),subst(e2))
      }
      case Binary(bop,e1,e2) => Binary(bop,subst(e1),subst(e2))
      case Unary(uop,e1) => Unary(uop,subst(e1))
      case If(e1,e2,e3) => If(subst(e1),subst(e2),subst(e3))
      case Function(Some(p),para,e1) => if (x != para && x != p) Function(Some(p),para,subst(e1)) else e
      case Function(None,para,e1) => if (x != para) Function(None,para,subst(e1)) else e
      case Call(e1,e2) => if (!isValue(e1)) Call(subst(e1),e2) else Call(e1,subst(e2))
      case _ => throw new UnsupportedOperationException
    }
  }
    
  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      
        // ****** Your cases here
      
      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
      
        // ****** Your cases here
      case ConstDecl(x,e1,e2) => if (!isValue(e1)) ConstDecl(x,step(e1),e2) else substitute(e2,e1,x)
      case Unary(uop,e1) => unaryStep(uop,e1)
      case Binary(bop,e1,e2) => binaryStep(bop,e1,e2)
      case If(e1,e2,e3) => if (!isValue(e1)) If(step(e1),e2,e3) else if (toBoolean(e1)) e2 else e3
      case Call(e1,e2) =>  e1 match {
        case Function(None,x,func) if (isValue(e1) && isValue(e2)) => substitute(func,e2,x)
        case Function(Some(p),x,func) if (isValue(e1) && isValue(e2)) => substitute(substitute(func,e1,p),e2,x)
        case _ if (!isValue(e2)) => Call(e1,step(e2))
        case _ if (!isValue(e1)) => Call(step(e1),e2)
        case _ => throw DynamicTypeError(e1)
      } 
      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }
  
  def unaryStep(uop:Uop, e:Expr):Expr = uop match {
    case Neg => if (isValue(e)) N(-toNumber(e)) else Unary(uop,step(e))
    case Not => if (isValue(e)) B(!toBoolean(e)) else Unary(Not,e)
  }
  
  def isEqual(e1:Expr, e2:Expr): Boolean = (e1,e2) match {
	  case (S(s1),S(s2)) => s1 == s2
	  case (B(b1),B(b2)) => b1 == b2
	  case (N(n1),N(n2)) => n1 == n2
	  case (Function(_,_,_),_) => throw DynamicTypeError(e1)
	  case (_,Function(_,_,_)) => throw DynamicTypeError(e2)
	  case _ => false
  }
  
  def binaryStep(bop:Bop,e1:Expr,e2:Expr):Expr = {
    /*
     * Wrote this because original implementation did not conform to the
     * DoSeq rule. We're also too lazy to rewrite it but we will for lab 4.
     */
    bop match {
      case Or => {
        if (isValue(e1)) {
          if (toBoolean(e1)) e1 else e2
        } else Binary(Or,step(e1),e2)
      } case And => {
        if (isValue(e1)) {
          if (toBoolean(e1)) e2 else e1
        } else Binary(And,step(e1),e2)
      } case Eq => {
        if (!isValue(e1)) Binary(Eq,step(e1),e2)
        else if (!isValue(e2)) Binary(Eq,e1,step(e2))
        else B(isEqual(e1,e2))
      } case Ne => {
        if (!isValue(e1)) Binary(Ne,step(e1),e2)
        else if (!isValue(e2)) Binary(Ne,e1,step(e2))
        else B(!isEqual(e1,e2))
      } case Lt => (e1,e2) match {
        case (e1,e2) if (!isValue(e1)) => Binary(Lt,step(e1),e2)
        case (e1,e2) if (!isValue(e2)) => Binary(Lt,e1,step(e2))
        case (S(_),S(_)) => B(toStr(e1) < toStr(e2))
        case _ => B(toNumber(e1) < toNumber(e2))
      } case Le => (e1,e2) match {
        case (e1,e2) if (!isValue(e1)) => Binary(Le,step(e1),e2)
        case (e1,e2) if (!isValue(e2)) => Binary(Le,e1,step(e2))
        case (S(_),S(_)) => B(toStr(e1) <= toStr(e2))
        case _ => B(toNumber(e1) <= toNumber(e2))
      } case Gt => (e1,e2) match {
        case (e1,e2) if (!isValue(e1)) => Binary(Gt,step(e1),e2)
        case (e1,e2) if (!isValue(e2)) => Binary(Gt,e1,step(e2))
        case (S(_),S(_)) => B(toStr(e1) > toStr(e2))
        case _ => B(toNumber(e1) > toNumber(e2))
      } case Ge => (e1,e2) match {
        case (e1,e2) if (!isValue(e1)) => Binary(Ge,step(e1),e2)
        case (e1,e2) if (!isValue(e2)) => Binary(Ge,e1,step(e2))
        case (S(_),S(_)) => B(toStr(e1) >= toStr(e2))
        case _ => B(toNumber(e1) >= toNumber(e2))
      }
      
      case Plus => (e1,e2) match {
        case (e1,e2) if (!isValue(e1)) => Binary(Plus,step(e1),e2)
        case (e1,e2) if (!isValue(e2)) => Binary(Plus,e1,step(e2))
        case (S(_),_) | (_,S(_)) => S(toStr(e1) + toStr(e2)) //If either argument is a string program should return a concatenated string
		case _ => N(toNumber(e1) + toNumber(e2))
      } case Minus => (e1,e2) match {
        case (e1,e2) if (!isValue(e1)) => Binary(Minus,step(e1),e2)
        case (e1,e2) if (!isValue(e2)) => Binary(Minus,e1,step(e2))
        case _ => N(toNumber(e1) - toNumber(e2))
      } case Times => (e1,e2) match {
        case (e1,e2) if (!isValue(e1)) => Binary(Times,step(e1),e2)
        case (e1,e2) if (!isValue(e2)) => Binary(Times,e1,step(e2))
        case _ => N(toNumber(e1) * toNumber(e2))
      } case Div => (e1,e2) match {
        case (e1,e2) if (!isValue(e1)) => Binary(Div,step(e1),e2)
        case (e1,e2) if (!isValue(e2)) => Binary(Div,e1,step(e2))
        case _ => N(toNumber(e1) / toNumber(e2))
      }
      
      case Seq => if (!isValue(e1)) Binary(Seq,step(e1),e2) else e2
    }
  }
  

  /* External Interfaces */
  
  this.debug = true // comment this out or set to false if you don't want print debugging information
  
  // Interface to run your big-step interpreter starting from an empty environment and print out
  // the test input if debugging.
  def evaluate(e: Expr): Expr = {
    require(closed(e))
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with eval ...")
      println("\nExpression:\n  " + e)
    }
    val v = eval(emp, e)
    if (debug) {
      println("Value: " + v)
    }
    v
  } 
  
  // Convenience to pass in a jsy expression as a string.
  def evaluate(s: String): Expr = evaluate(jsy.lab3.Parser.parse(s))
   
  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging. 
  def iterateStep(e: Expr): Expr = {
    require(closed(e))
    def loop(e: Expr, n: Int): Expr = {
      if (debug) { println("Step %s: %s".format(n, e)) }
      if (isValue(e)) e else loop(step(e), n + 1)
    }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val v = loop(e, 0)
    if (debug) {
      println("Value: " + v)
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(jsy.lab3.Parser.parse(s))
  
  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }
    
    val expr =
      handle(None: Option[Expr]) {Some{
        jsy.lab3.Parser.parseFile(file)
      }} getOrElse {
        return
      }
    
    handle() {
      val v = evaluate(expr)
      println(pretty(v))
    }
    
    handle() {
      val v1 = iterateStep(expr)
      println(pretty(v1))
    }
  }
    
}
