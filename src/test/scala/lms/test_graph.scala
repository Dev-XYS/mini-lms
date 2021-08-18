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

  test("simple lambda") {
    val snippet = new Frontend {
      def main(store: Rep[Int]) = {
        // val f = fun { (a: Rep[Int]) =>
        //   {
        //     a
        //   }
        // }
        val f = fun { (a: Rep[Int]) =>
          val c = alloc(store)
          val g = fun { (b: Rep[Int]) => c }
          g
        }
      }

      lazy val graph = getGraph(main)
    }

    println(snippet.graph)
  }

  test("escaping ref") {
    val snippet = new Frontend {
      def main(store: Rep[Int]) = {
        val f = fun { (a: Rep[Int]) =>
          val c = alloc(store)
          val g = fun { (b: Rep[Int]) => c }
          g
        }
        val h0 = f(0)
        val h1 = f(1)
        val c0 = h0(0)
        val c1 = h0(1) // same as c0
        val c3 = h1(0)
        val c4 = h1(1) // same as c3
        inc(c0)
        inc(c1)
        inc(c3)
        inc(c4)
        get(c0)
        // expected result:
        // - ops on c0 and c1 are serialized
        // - c3 and c4 are never read and hence
        //   dce'd along with all their ops
      }

      lazy val graph = getGraph(main)
    }

    println(snippet.graph)
  }
}
