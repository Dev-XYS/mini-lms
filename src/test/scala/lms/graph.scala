package lms

import collection.mutable.Map

object Data {

  val graph = Map[String, String]()

  graph("basic println") = """====================
x1 = 1, type: #
x2 = print(x0 x1), type: #, deps: {  }
x3 = 2, type: #
x4 = print(x0 x3), type: #, deps: {  }
x5 = 0, type: #
--------------------
Block(in: [x0], result: x5, effect: { init: [], read: [], write: [x0], kill: [] }, deps: {  })
====================
"""

  graph("basic dce 1") = """====================
x1 = alloc(x0), type: #^{x1}, deps: {  }
x2 = alloc(x0), type: #^{x2}, deps: {  }
x3 = get(x2), type: #, deps: {  }
x4 = get(x1), type: #, deps: {  }
--------------------
Block(in: [x0], result: x4, effect: { init: [x1 x2], read: [x0 x2 x1], write: [], kill: [] }, deps: {  })
====================
"""

  graph("basic dce 2") = """====================
x1 = alloc(x0), type: #^{x1}, deps: {  }
x2 = 0, type: #
x3 = set(x1 x2), type: #, deps: {  }
x4 = get(x1), type: #, deps: {  }
x5 = 1, type: #
x6 = set(x1 x5), type: #, deps: {  }
x7 = get(x1), type: #, deps: {  }
x8 = get(x1), type: #, deps: {  }
--------------------
Block(in: [x0], result: x8, effect: { init: [], read: [x0 x1], write: [x1], kill: [] }, deps: {  })
====================
"""

  graph("escaping ref") = """====================
x3 = alloc(x0), type: #^{x3}, deps: {  }
x4 = λ(Block(in: [x5], result: x3, effect: { init: [], read: [], write: [], kill: [] }, deps: {  })), type: x4(x5:#^{} => #^{x3})^{x3 x4} ^^{ init: [], read: [], write: [], kill: [] }, deps: {  }
x1 = λ(Block(in: [x2], result: x4, effect: { init: [x3], read: [x0], write: [], kill: [] }, deps: {  })), type: x1(x2:#^{} => x4(x5:#^{} => #^{x4})^{} ^^{ init: [], read: [], write: [], kill: [] })^{x0 x1} ^^{ init: [], read: [x0], write: [], kill: [] }, deps: {  }
x6 = 0, type: #
x7 = @(x1 x6), type: x4(x5:#^{} => #^{x4})^{x7} ^^{ init: [], read: [], write: [], kill: [] }, deps: {  }
x8 = 1, type: #
x9 = @(x1 x8), type: x4(x5:#^{} => #^{x4})^{x9} ^^{ init: [], read: [], write: [], kill: [] }, deps: {  }
x10 = 0, type: #
x11 = @(x7 x10), type: #^{x7 x11}, deps: {  }
x12 = 1, type: #
x13 = @(x7 x12), type: #^{x7 x13}, deps: {  }
x14 = 0, type: #
x15 = @(x9 x14), type: #^{x9 x15}, deps: {  }
x16 = 1, type: #
x17 = @(x9 x16), type: #^{x9 x17}, deps: {  }
x18 = inc(x11), type: #, deps: {  }
x19 = inc(x13), type: #, deps: {  }
x20 = inc(x15), type: #, deps: {  }
x21 = inc(x17), type: #, deps: {  }
x22 = get(x11), type: #, deps: {  }
--------------------
Block(in: [x0], result: x22, effect: { init: [x1], read: [x0 x7 x11], write: [x17 x7 x13 x11 x15 x9], kill: [] }, deps: {  })
====================
"""
}
