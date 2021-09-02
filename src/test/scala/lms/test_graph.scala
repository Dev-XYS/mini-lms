package lms

import org.scalatest.FunSuite

abstract class Snippet extends Frontend {

  def main(x: Rep): Rep

  lazy val graph = getGraph(main)
}

class GraphTests extends FunSuite {

  test("basic println") {
    val snippet = new Snippet {
      def main(stdout: Rep) = {
        print(stdout, 1)
        print(stdout, 2)
        0
      }
    }

    println(snippet.graph)
  }

  test("basic dce 1") {
    val snippet = new Snippet {
      def main(store: Rep) = {
        val c = alloc(store)
        val d = alloc(store) // dce
        get(d) // dce
        get(c)
      }
    }

    println(snippet.graph)
  }

  test("basic dce 2") {
    val snippet = new Snippet {
      def main(store: Rep) = {
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
    val snippet = new Snippet {
      def main(store: Rep) = {
        val f = fun() { (a: Rep) =>
          val c = alloc(store)
          val g = fun() { (b: Rep) => c }
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
    val snippet = new Snippet {
      def main(store: Rep) = {
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
    val snippet = new Snippet {
      def main(store: Rep) = {
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
    val snippet = new Snippet {
      def main(store: Rep) = {
        val myfree = fun() { (c: Rep) =>
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

  test("effect polymorphism 1") {
    val snippet = new Snippet {
      def main(store: Rep) = {
        // rwk is an abbreviation for read, write, kill
        // result type: Int @call(f)
        val gen = fun(rwk) { (f: Rep) =>
          f(1)
        }
        val g = fun() { (x: Rep) =>
          {
            print(store, x)
            x
          }
        }
        val res = gen(g) // effect: @call(g), doesn't really kill g or store!
        print(store, 1)
      }
    }

    println(snippet.graph)
  }

  test("Example 1: Tracking Independent Heap Objects") {
    val snippet = new Snippet {
      def main(world: Rep) = {
        val counter = fun() { (unit: Rep) =>
          val c = alloc(world)
          fun() { (unit: Rep) => inc(c) }
        }
        val inc1 = counter()
        val inc2 = counter()
        inc1()
        inc1()
        inc2()
        inc2()
        // uncomment the following lines one by one
        // and watch the target code change:
        inc2()
        // inc1()
        // inc1() + inc2()
        // 0
      }
    }

    println(snippet.graph)
  }
}
