package lms

import org.scalatest.FunSuite

abstract class Snippet[A, B] extends Frontend {

  def main(x: Rep[A]): Rep[B]

  lazy val graph = getGraph(main)
}

class GraphTests extends FunSuite {

  test("basic println") {
    val snippet = new Snippet[Int, Int] {
      def main(stdout: Rep[Int]) = {
        print(stdout, 1)
        print(stdout, 2)
        0
      }
    }

    println(snippet.graph)
  }

  test("basic dce 1") {
    val snippet = new Snippet[Int, Int] {
      def main(store: Rep[Int]) = {
        val c = alloc(store)
        val d = alloc(store) // dce
        get(d) // dce
        get(c)
      }
    }

    println(snippet.graph)
  }

  test("basic dce 2") {
    val snippet = new Snippet[Int, Int] {
      def main(store: Rep[Int]) = {
        val c = alloc(store)
        set(c, 0) // dce
        get(c) // dce
        set(c, 1)
        get(c) // dce
        get(c)
      }
    }

    println(snippet.graph)
  }

  test("escaping ref") {
    val snippet = new Snippet[Int, Int] {
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
    }

    println(snippet.graph)
  }

  test("compact codegen soft deps") {
    val snippet = new Snippet[Int, Int] {
      def main(store: Rep[Int]) = {
        val c = alloc(store)
        val r = get(c) // may not move after inc
        inc(c)
        print(store, get(c))
        r // tempting to inline r here
      }
    }

    println(snippet.graph)
  }

  test("consume effects 1") {
    val snippet = new Snippet[Int, Int] {
      def main(store: Rep[Int]) = {
        val c = alloc(store)
        inc(c)
        print(store, get(c))
        free(c)
        get(c) // error
      }
    }

    println(snippet.graph)
  }

  test("consume effects 2") {
    val snippet = new Snippet[Int, Int] {
      def main(store: Rep[Int]) = {
        val myfree = fun { (c: Rep[Int]) =>
          free(c)
        }
        val c = alloc(store)
        inc(c)
        print(store, get(c))
        myfree(c)
        get(c) // error
      }
    }

    println(snippet.graph)
  }
}
