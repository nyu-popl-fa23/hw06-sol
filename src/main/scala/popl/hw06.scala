package popl

import js.ast._
import js.parse
import js.util.JsApp
import Bop._, Uop._

object hw06 extends JsApp:

  import scala.util.parsing.input.NoPosition

  /*
   * CSCI-UA.0480-055: Homework 6
   *
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your solution will _not_ be graded if it does not compile!!
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * '???' as needed to get something that compiles without error.
   *
   */

  /* JakartaScript */

  // Value environments
  type Env = Map[String, Val]

  def emp: Env = Map()

  def get(env: Env, x: String): Val = env.getOrElse(x, Undefined)

  def extend(env: Env, x: String, v: Val): Env = env + (x -> v)

  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   */

  def toNum(v: Val): Double =
    v match
      case Num(n) => n
      case Bool(false) => 0
      case Bool(true) => 1
      case Undefined => Double.NaN
      case Str(s) => try s.toDouble catch
        case _: Throwable => Double.NaN
      case Function(_, _, _) => Double.NaN

  def toBool(v: Val): Boolean =
    v match
      case Num(n) if (n compare 0.0) == 0 || (n compare -0.0) == 0 || n.isNaN => false
      case Num(_) => true
      case Bool(b) => b
      case Undefined => false
      case Str("") => false
      case Str(_) => true
      case Function(_, _, _) => true

  def toStr(v: Val): String =
    v match
      case Num(n) => if n.isWhole then "%.0f" format n else n.toString
      case Bool(b) => b.toString
      case Undefined => "undefined"
      case Str(s) => s
      case Function(_, _, _) => "function"

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   */
  def inequalityVal(bop: Bop, v1: Val, v2: Val): Boolean =
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match
      case (Str(s1), Str(s2)) =>
        (bop: @unchecked) match
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
      case _ =>
        val (n1, n2) = (toNum(v1), toNum(v2))
        (bop: @unchecked) match
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2

  /*
   * This code is a reference implementation of JakartaScript without
   * functions (i.e., Homework 4). You are welcome to replace it with your
   * code from Homework 4.
   */
  def eval(env: Env, e: Expr): Val =
    /* Some helper functions for convenience. */
    def eToNum(e: Expr): Double = toNum(eval(env, e))

    def eToBool(e: Expr): Boolean = toBool(eval(env, e))

    def eToVal(e: Expr): Val = eval(env, e)

    e match
      /* Base Cases */

      // EvalVal
      case v: Val => v

      // EvalVar
      case Var(x) => get(env, x)

      /* Inductive Cases */

      // EvalPrint
      case Print(e) =>
        println(eToVal(e).prettyVal)
        Undefined

      // EvalUMinus
      case UnOp(UMinus, e1) => Num(-eToNum(e1))

      // EvalNot
      case UnOp(Not, e1) => Bool(!eToBool(e1))

      // EvalPlus*
      case BinOp(Plus, e1, e2) => (eToVal(e1), eToVal(e2)) match
        // EvalPlusStr1
        case (Str(s1), v2) => Str(s1 + toStr(v2))
        // EvalPlusStr2
        case (v1, Str(s2)) => Str(toStr(v1) + s2)
        // EvalPlusNum
        case (v1, v2) => Num(toNum(v1) + toNum(v2))

      // EvalArith
      case BinOp(Minus, e1, e2) => Num(eToNum(e1) - eToNum(e2))
      case BinOp(Times, e1, e2) => Num(eToNum(e1) * eToNum(e2))
      case BinOp(Div, e1, e2) => Num(eToNum(e1) / eToNum(e2))

      // EvalEqual, EvalTypeErrorEqual1, EvalTypeErrorEqual2
      case BinOp(bop@(Eq | Ne), e1, e2) =>
        def checkFun(v: Expr): Unit = v match
          case Function(_, _, _) => throw DynamicTypeError(e)
          case _ => ()

        val v1 = eToVal(e1)
        checkFun(v1)
        val v2 = eToVal(e2)
        checkFun(v2)
        (bop: @unchecked) match
          case Eq => Bool(v1 == v2)
          case Ne => Bool(v1 != v2)

      // EvalAnd*
      case BinOp(And, e1, e2) =>
        val v1 = eToVal(e1)
        if toBool(v1) then /* EvalAndTrue */ eToVal(e2)
        else /* EvalAndFalse */ v1

      // EvalOr*
      case BinOp(Or, e1, e2) =>
        val v1 = eToVal(e1)
        if toBool(v1) then /* EvalOrTrue */ v1 else /* EvalOrFalse */ eToVal(e2)

      // EvalSeq
      case BinOp(Seq, e1, e2) => eToVal(e1); eToVal(e2)

      // EvalInequalNum1, EvalInequalNum2, EvalInequalStr
      case BinOp(bop, e1, e2) =>
        Bool(inequalityVal(bop, eToVal(e1), eToVal(e2)))

      // EvalIf*
      case If(e1, e2, e3) =>
        if eToBool(e1) then /* EvalIfThen */ eToVal(e2)
        else /* EvalIfElse */ eToVal(e3)

      // EvalConstDecl
      case ConstDecl(x, ed, eb) =>
        eval(extend(env, x, eToVal(ed)), eb)

      // EvalCall, EvalCallRec, EvalTypeErrorCall
      case Call(e1, e2) =>
        val v1 = eToVal(e1)
        v1 match
          case Function(p, x, e) =>
            val v2 = eToVal(e2)
            val env1 = p match
              case None =>
                // update env according to rule EvalCall
                extend(env, x, v2)
              case Some(x1) =>
                // update env according to rule EvalCallRec
                extend(extend(env, x1, v1), x, v2)
            eval(env1, e)
          case _ => throw DynamicTypeError(e)

        v1 match
          case Function(p, x2, e) =>
            val v2 = eToVal(e2)
            val env1 = p match
              case None => env
              case Some(x1) => extend(env, x1, v1)
            val env2 = extend(env1, x2, v2)
            eval(env2, e)
          case _ => throw DynamicTypeError(e)


  // Interface to run your big-step interpreter starting from an empty environment and print out
  // the test input if debugging.
  def evaluate(e: Expr): Val =
    require(closed(e))
    if debug then
      println("------------------------------------------------------------")
      println("Evaluating with eval ...")
      println(s"\nExpression:\n $e")
    val v = eval(emp, e)
    if debug then
      println(s"Value: $v")
    v

  // Interface to run your interpreter from a string.  This is convenient
  // for unit testing.
  def evaluate(s: String): Val = eval(emp, parse.fromString(s))


  /* Small-Step Interpreter with Static Scoping */
  def subst(e: Expr, x: String, v: Val): Expr =
    require(closed(v))

    /* Simple helper that calls substitute on an expression
     * with the input value v and variable name x. */
    def substX(e: Expr): Expr = subst(e, x, v)
    /* Body */
    e match
      case Num(_) | Bool(_) | Undefined | Str(_) => e
      case Print(e1) => Print(substX(e1))
      case UnOp(uop, e1) =>
        UnOp(uop, substX(e1))
      case BinOp(bop, e1, e2) =>
        BinOp(bop, substX(e1), substX(e2))
      case If(e1, e2, e3) =>
        If(substX(e1), substX(e2), substX(e3))
      case Var(y) =>
        if (x == y) v else e
      case ConstDecl(y, e1, e2) =>
        ConstDecl(y, substX(e1), if x == y then e2 else substX(e2))
      case Function(p, y, e1) =>
        Function(p, y, if x == y || p.contains(x) then e1 else substX(e1))
      case Call(e1, e2) =>
        Call(substX(e1), substX(e2))

  def step(e: Expr): Expr =
    e match
      /* Base Cases: Do Rules */

      // DoPrint
      case Print(v: Val) =>
        if debug then println("Applying rule DoPrint")
        println(v.prettyVal)
        Undefined

      // DoUMinus
      case UnOp(UMinus, v: Val) =>
        if debug then println("Applying rule DoUMinus")
        Num(-toNum(v))

      // TODO: add missing do rules here...

      // DoNot
      case UnOp(Not, v: Val) =>
        if debug then println("Applying rule DoNot")
        Bool(!toBool(v))

      // DoSeq
      case BinOp(Seq, _: Val, e2) =>
        if debug then println("Applying rule DoSeq")
        e2

      // DoPlusStr1
      case BinOp(Plus, Str(s1), v2: Val) =>
        if debug then println("Applying rule DoPlusStr1")
        Str(s1 + toStr(v2))

      // DoPlusStr2
      case BinOp(Plus, v1: Val, Str(s2)) =>
        if debug then println("Applying rule DoPlusStr2")
        Str(toStr(v1) + s2)

      // DoArith
      case BinOp(bop@(Plus | Minus | Times | Div), v1: Val, v2: Val) =>
        if debug then println("Applying rule DoArith")
        val op: (Double, Double) => Double = (bop: @unchecked) match
          case Plus => _ + _
          case Minus => _ - _
          case Times => _ * _
          case Div => _ / _
        Num(op(toNum(v1), toNum(v2)))

      // DoInequalNum*, DoInequalStr
      case BinOp(bop@(Lt | Le | Gt | Ge), v1: Val, v2: Val) =>
        if debug then println("Applying rule DoInequal*")
        Bool(inequalityVal(bop, v1, v2))

      // TypeErrorEqual1
      case BinOp(Eq | Ne, Function(_, _, _), _) =>
        if debug then println("Applying rule TypeErrorEqual1")
        throw DynamicTypeError(e)

      // TypeErrorEqual2
      case BinOp(Eq | Ne, _, Function(_, _, _)) =>
        if debug then println("Applying rule TypeErrorEqual2")
        throw DynamicTypeError(e)

      // DoEqual(===)
      case BinOp(Eq, v1: Val, v2: Val) =>
        if debug then println("Applying rule DoEqual(===)")
        Bool(v1 == v2)

      // DoEqual(!==)
      case BinOp(Ne, v1: Val, v2: Val) =>
        if debug then println("Applying rule DoEqual(!==)")
        Bool(v1 != v2)

      // DoAnd*
      case BinOp(And, v1: Val, e2) =>
        if toBool(v1) then
          if debug then println("Applying rule DoAndTrue")
          e2
        else
          if debug then println("Applying rule DoAndFalse")
          v1

      // DoOr*
      case BinOp(Or, v1: Val, e2) =>
        if toBool(v1) then
          if debug then println("Applying rule DoOrTrue")
          v1
        else
          if debug then println("Applying rule DoOrFalse")
          e2

      // DoConstDecl
      case ConstDecl(x, v1: Val, e2) =>
        if debug then println("Applying rule DoConst")
        subst(e2, x, v1)

      // DoIf*
      case If(v1: Val, e2, e3) =>
        if toBool(v1) then
          if debug then println("Applying rule DoIfThen")
          e2
        else
          if debug then println("Applying rule DoIfElse")
          e3

      // TypeErrorCall
      case Call(Num(_) | Bool(_) | Str(_) | Undefined, _) =>
        if debug then println("Applying rule TypeErrorCall")
        throw DynamicTypeError(e)

      // DoCall*
      case Call(v1@Function(p, x2, e1), v2: Val) =>
        p match
          case None =>
            if debug then println("Applying rule DoCall")
            subst(e1, x2, v2)
          case Some(x1) =>
            if debug then println("Applying rule DoCallRec")
            subst(subst(e1, x1, v1), x2, v2)

      /* Inductive Cases: Search Rules */

      // SearchPrint
      case Print(e) =>
        if debug then println("Applying rule SearchPrint")
        Print(step(e))

      // SearchUop
      case UnOp(uop, e) =>
        if debug then println("Applying rule SearchUop")
        UnOp(uop, step(e))

      // SearchBop2, SearchEqual
      case BinOp(bop, v1: Val, e2) =>
        if debug then bop match
          case Eq | Ne => println("Applying rule SearchEqual")
          case _ => println("Applying rule SearchBop2")
        BinOp(bop, v1, step(e2))

      // SearchBop1
      case BinOp(bop, e1, e2) =>
        if debug then println("Applying rule SearchBop1")
        BinOp(bop, step(e1), e2)

      // SearchIf
      case If(e1, e2, e3) =>
        if debug then println("Applying rule SearchIf")
        If(step(e1), e2, e3)

      // SearchConst
      case ConstDecl(x, e1, e2) =>
        if debug then println("Applying rule SearchConst")
        ConstDecl(x, step(e1), e2)

      // SearchCall2
      case Call(v1: Val, e2) =>
        if debug then println("Applying rule SearchCall2")
        Call(v1, step(e2))

      // SearchCall1
      case Call(e1, e2) =>
        if debug then println("Applying rule SearchCall1")
        Call(step(e1), e2)

      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw AssertionError("Internal error: not a closed expression:\n%s".format(e))
      case _: Val => throw AssertionError("Internal error: step should not be called on values:\n%s".format(e))

  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging.
  def iterateStep(e: Expr): Val =
    require(closed(e))

    def loop(e: Expr, n: Int): Val =
      if debug then
        println(s"Step $n: $e")
      
      e match
        case v: Val => v
        case e =>
          // take a step
          val ep = step(e)
          // preserve source code position of e if possible
          val epp = if ep.pos != NoPosition then ep else ep.setPos(e.pos)
          // and continue evaluation
          loop(epp, n + 1)

    if debug then
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
      
    val v = loop(e, 0)
    if debug then
      println("Value: " + v)
    v

  // Convenience function to pass in a js expression as a string.
  def iterateStep(s: String): Val = iterateStep(parse.fromString(s))

  /* Interface to run your interpreter from the command line.  You can ignore the code below. */

  def processFile(file: java.io.File): Unit =
    if debug then
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")

    val expr = handle(fail()) {
      parse.fromFile(file)
    }

    if debug then
      println("Parsed expression:")
      println(expr)

    handle(()) {
      val v = evaluate(expr)
      println(v.prettyVal)
    }

    handle(()) {
      val v1 = iterateStep(expr)
      println(v1.prettyVal)
    }
