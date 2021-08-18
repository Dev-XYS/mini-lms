package lms

import org.scalatest.FunSuite

class GraphTests extends FunSuite {

  test("basic println") {
    val snippet = new Frontend {
      def f(stdout: Rep[Int]) = {
        print(stdout, 1)
        print(stdout, 2)
        0
      }

      lazy val graph = getGraph(f)
    }

    println(snippet.graph)
  }

  test("basic dce 1") {
    val snippet = new Frontend {
      def f(store: Rep[Int]) = {
        val c = alloc(store)
        val d = alloc(store) // dce
        get(d) // dce
        get(c)
      }

      lazy val graph = getGraph(f)
    }

    println(snippet.graph)
  }

  test("basic dce 2") {
    val snippet = new Frontend {
      def f(store: Rep[Int]) = {
        val c = alloc(store)
        set(c, 0) // dce
        get(c) // dce
        set(c, 1)
        get(c) // dce
        get(c)
      }

      lazy val graph = getGraph(f)
    }

    println(snippet.graph)
  }
}
