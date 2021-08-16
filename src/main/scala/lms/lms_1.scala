package lms

trait lms_1 {

  trait Exp {}

  case class Lit(i: Int) extends Exp {}
  case class Lit2(i: Int) extends Exp {}
  case class Var(x: Int) extends Exp {}
  case class Var2(x: Int) extends Exp {}
  case class Let(v: Exp, body: Exp) extends Exp {}
  case class Let2(v: Exp, body: Exp) extends Exp {}
  case class Lam(body: Exp) extends Exp {}
  case class Lam2(body: Exp) extends Exp {}
  case class App(e1: Exp, e2: Exp) extends Exp {}
  case class App2(e1: Exp, e2: Exp) extends Exp {}
  case object Tic extends Exp {}
  case object Tic2 extends Exp {}
  case class Plus(e1: Exp, e2: Exp) extends Exp {}
  case class Plus2(e1: Exp, e2: Exp) extends Exp {}
  case class Minus(e1: Exp, e2: Exp) extends Exp {}
  case class Minus2(e1: Exp, e2: Exp) extends Exp {}
  case class Ifz(e1: Exp, e2: Exp, e3: Exp) extends Exp {}
  case class Ifz2(e1: Exp, e2: Exp, e3: Exp) extends Exp {}

  trait Val {}
  type Env = List[Val]

  case class Cst(i: Int) extends Val {}
  case class Clo(env: Env, e: Exp) extends Val {}
  case class Code(e: Exp) extends Val {}

  var stC = 0
  def tick() = { stC += 1; stC - 1 }
  def eval(env: Env, e: Exp): Val = e match {
    case Lit(n)      => Cst(n)
    case Var(n)      => env(n)
    case Tic         => Cst(tick())
    case Lam(e)      => Clo(env, e)
    case Let(e1, e2) => eval(env :+ eval(env, e1), e2)
    case App(e1, e2) =>
      val Clo(env3, e3) = eval(env, e1)
      eval(env3 :+ eval(env, e2), e3)
  }

  var stFresh = 0
  var stBlock: List[Exp] = Nil
  var stFun: List[(Int, Env, Exp)] = Nil
  def run[A](f: => A): A = {
    val sF = stFresh
    val sB = stBlock
    val sN = stFun
    try f
    finally { stFresh = sF; stBlock = sB; stFun = sN; }
  }

  def fresh() = { stFresh += 1; Var(stFresh - 1) }
  def reflect(s: Exp) = { stBlock :+= s; fresh() }
  def reify(f: => Exp) = run {
    stBlock = Nil; val last = f; stBlock.foldRight(last)(Let)
  }

  def anf(env: List[Exp], e: Exp): Exp = e match {
    case Lit(n)      => Lit(n)
    case Var(n)      => env(n)
    case Tic         => reflect(Tic)
    case Lam(e)      => reflect(Lam(reify(anf(env :+ fresh(), e))))
    case App(e1, e2) => reflect(App(anf(env, e1), anf(env, e2)))
    case Let(e1, e2) => anf(env :+ (anf(env, e1)), e2)
  }

  def freshc() = Code(fresh())
  def reflectc(s: Exp) = Code(reflect(s))
  def reifyc(f: => Val) = reify { val Code(r) = f; r }

  def evalms(env: Env, e: Exp): Val = {
    e match {
      case Lit(n)      => Cst(n)
      case Var(n)      => env(n)
      case Tic         => Cst(tick())
      case Lam(e)      => Clo(env, e)
      case Let(e1, e2) => evalms(env :+ evalms(env, e1), e2)
      case App(e1, e2) =>
        val Clo(env3, e3) = evalms(env, e1)
        val v2 = evalms(env, e2)
        evalms(env3 :+ Clo(env3, e3) :+ v2, e3)
      case Plus(e1, e2) =>
        val Cst(v1) = evalms(env, e1)
        val Cst(v2) = evalms(env, e2)
        Cst(v1 + v2)
      case Minus(e1, e2) =>
        val Cst(v1) = evalms(env, e1)
        val Cst(v2) = evalms(env, e2)
        Cst(v1 - v2)
      case Ifz(e1, e2, e3) =>
        val Cst(v1) = evalms(env, e1)
        if (v1 == 0) evalms(env, e2) else evalms(env, e3)
      case Lit2(n) => Code(Lit(n))
      case Var2(n) => env(n)
      case Tic2    => reflectc(Tic)
      case Lam2(e) =>
        stFun collectFirst { case (n, `env`, `e`) => n } match {
          case Some(n) =>
            Code(Var(n))
          case None =>
            stFun :+= (stFresh, env, e)
            reflectc(Lam(reifyc(evalms(env :+ freshc() :+ freshc(), e))))
        }
      case Let2(e1, e2) => evalms(env :+ evalms(env, e1), e2)
      case App2(e1, e2) =>
        val Code(s1) = evalms(env, e1)
        val Code(s2) = evalms(env, e2)
        reflectc(App(s1, s2))
      case Plus2(e1, e2) =>
        val Code(s1) = evalms(env, e1)
        val Code(s2) = evalms(env, e2)
        reflectc(Plus(s1, s2))
      case Minus2(e1, e2) =>
        val Code(s1) = evalms(env, e1)
        val Code(s2) = evalms(env, e2)
        reflectc(Minus(s1, s2))
      case Ifz2(e1, e2, e3) =>
        val Code(s1) = evalms(env, e1)
        val Code(s2) = evalms(env, e2)
        val Code(s3) = evalms(env, e3)
        reflectc(Ifz(s1, s2, s3))
    }
  }

}

object Main_1 extends lms_1 {
  def main(args: Array[String]): Unit = {
    val e_ack =
      Let(
        Lam(
          Lam2(
            Ifz(
              Var(1),
              Plus2(Var(3), Lit2(1)),
              Ifz2(
                Var(3),
                App2(App(Var(0), Minus(Var(1), Lit(1))), Lit2(1)),
                App2(
                  App(Var(0), Minus(Var(1), Lit(1))),
                  App2(App(Var(0), Var(1)), Minus2(Var(3), Lit2(1)))
                )
              )
            )
          )
        ),
        App(Var(0), Lit(2))
      )
    println(s"[result] ${reifyc(evalms(Nil, e_ack))}")
  }
}
