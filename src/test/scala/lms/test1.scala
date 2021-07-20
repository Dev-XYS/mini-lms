package lms

import org.scalatest.FunSuite

class HelloTests extends FunSuite with lms {

  // test 1
  test("literal") {
    val e = new Lit(1)
    assert(evalms(List(), e) == new Cst(1))
  }

}
