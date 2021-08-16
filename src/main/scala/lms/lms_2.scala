package lms

import java.io._

trait lms_2 {

  trait Exp {}

  case class Lit(i: Int) extends Exp {}
  case class Var(x: Int) extends Exp {}
  case class Let(v: Exp, body: Exp) extends Exp {}
  case class Lam(body: Exp) extends Exp {}
  case class App(e1: Exp, e2: Exp) extends Exp {}
  case object Tic extends Exp {}
  case class Plus(e1: Exp, e2: Exp) extends Exp {}
  case class Minus(e1: Exp, e2: Exp) extends Exp {}
  case class Ifz(e1: Exp, e2: Exp, e3: Exp) extends Exp {}

  trait Val {}

  type Env = List[Val]

  var stFresh = 0
  var stBlock: List[Exp] = Nil
  var stFun: List[(Int, Int)] = Nil

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

  type Rep[T] = Exp

  def lit(n: Int): Rep[Int] = Lit(n)
  def tic() = reflect(Tic)
  def lam[A, B](f: Rep[A] => Rep[B]): Rep[A => B] = {
    val baos = new ByteArrayOutputStream(1024)
    val oos = new ObjectOutputStream(baos)
    oos.writeObject(f)
    val ba = baos.toByteArray()
    val hash = ba.foldRight(0)(
      { (x, y) => (y * 256 + x) % 1000003 }
    ) // an unreliable hash function
    stFun collectFirst { case (n, `hash`) => n } match {
      case Some(n) =>
        Var(n)
      case None =>
        stFun :+= (stFresh, hash)
        val r = fresh()
        stBlock :+= Lam(reify(f(fresh())))
        r
    }
  }
  def app[A, B](f: Rep[A => B], x: Rep[A]): Rep[B] = reflect(App(f, x))
  def plus(a: Rep[Int], b: Rep[Int]): Rep[Int] = reflect(Plus(a, b))
  def minus(a: Rep[Int], b: Rep[Int]): Rep[Int] = reflect(Minus(a, b))
  def ifz[A](cond: Rep[Int], a: Rep[A], b: Rep[A]): Rep[A] = reflect(
    Ifz(cond, a, b)
  )

}

object Main_2 extends lms_2 {
  def main(args: Array[String]): Unit = {
    def ack: Int => Rep[Int => Int] = { m: Int =>
      lam { n: Rep[Int] =>
        {
          if (m == 0) plus(n, lit(1))
          else
            ifz(
              n,
              app(ack(m - 1), lit(1)),
              app(ack(m - 1), app(ack(m), minus(n, lit(1))))
            )
        }
      }
    }
    println(s"[result] ${reify(ack(2))}")
  }
}
