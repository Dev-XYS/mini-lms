package lms

import collection.mutable
import collection.mutable.{Set, Map}
import java.io._

object Backend {

  abstract class Def
  abstract class Exp extends Def

  case class Sym(n: Int) extends Exp {
    override def toString = s"x$n"
  }
  case class Const(x: Any) extends Exp {
    override def toString = x.toString
  }

  case class Node(n: Sym, op: String, rhs: List[Def], aliases: Set[Exp], deps: Dependency) {
    override def toString =
      if (op == "")
        // constant
        s"$n = ${rhs.mkString(" ")}"
      else
        // non-constant
        s"$n = $op(${rhs.mkString(" ")}), aliases: [${aliases.mkString(" ")}], deps: { $deps }"
  }

  case class Block(in: List[Sym], res: Exp, ein: Sym, eff: EffectSummary, deps: Dependency) extends Def {
    override def toString = s"in: [${in.mkString(" ")}], result: $res, effect: { $eff }, deps: { $deps }"
  }

  case class Dependency(var hdeps: Map[Exp, Set[Exp]], sdeps: Map[Exp, Set[Exp]]) {
    override def toString = s"hard: {${hdeps.mkString(" ")}}, soft: {${sdeps.mkString(" ")}}"
  }

  case class EffectSummary(init: Set[Exp], read: Set[Exp], write: Set[Exp], kill: Set[Exp]) {
    override def toString = s"init: [${init.mkString(" ")}], read: [${read.mkString(" ")}], write: [${write.mkString(" ")}], kill: [${kill.mkString(" ")}]"
  }

  case class Graph(nodes: List[Node], block: Block) {
    override def toString = {
      val source = new java.io.ByteArrayOutputStream()
      val stream = new java.io.PrintStream(source)
      stream.println("====================")
      for (node <- nodes)
        stream.println(node)
      stream.println("--------------------")
      stream.println(block)
      stream.println("====================")
      source.toString
    }
  }
}

import Backend._

class GraphBuilder {

  val globalDefs = mutable.ArrayBuffer[Node]()

  // begin local definitions

  var ein = Sym(-1);

  var initSym = Map[Exp, Exp]()
  var lastRead = Map[Exp, Set[Exp]]()
  var lastWrite = Map[Exp, Exp]()

  // end local definitions

  var nSyms = 0
  def fresh = try nSyms
  finally nSyms += 1

  def reflect(op: String, as: Def*)(aliases: Set[Exp], self: Boolean)(eff: EffectSummary, init: Boolean = false) = {
    val s = Sym(fresh)
    if (self) aliases += s

    // compute dependencies

    val hdeps = Map[Exp, Set[Exp]]()
    val sdeps = Map[Exp, Set[Exp]]()

    // update dependencies and states
    if (init) initSym(s) = s

    for (r <- eff.read) {
      hdeps.getOrElseUpdate(r, Set()) += lastWriteOrInit(r)
      lastRead.getOrElseUpdate(r, Set()) += s
    }

    for (w <- eff.write) {
      sdeps.getOrElseUpdate(w, Set()) += lastWriteOrInit(w)
      sdeps(w) ++= lastRead.getOrElse(w, Set()) - s
      lastWrite(w) = s
      lastRead(w) = Set()
    }

    // construct node
    val n = Node(s, op, as.toList, aliases, Dependency(hdeps, sdeps))
    globalDefs += n
    s
  }

  def reify(f: Exp => Exp) = withScope {
    // generate symbolic argument
    val x = Sym(fresh)

    // set current `ein` (for now, it is the same as the function argument)
    ein = x

    // execute the function
    val res = f(x)

    // compute dependencies for the whole block

    val hdeps = Map[Exp, Set[Exp]]()
    val sdeps = Map[Exp, Set[Exp]]()

    for ((key, rs) <- lastRead) {
      sdeps(key) = rs
    }

    for ((key, w) <- lastWrite) {
      hdeps(key) = Set(w)
    }

    // return a block
    Block(List(x), res, x, EffectSummary(Set(), Set(lastRead.keys.toSeq: _*), Set(lastWrite.keys.toSeq: _*), Set()), Dependency(hdeps, sdeps))
  }

  def lastWriteOrInit(x: Exp) = {
    lastWrite.getOrElse(x, initSym.getOrElse(x, ein))
  }

  def withScope(closure: => Block) = {
    // scoping: save the current environment
    val save_ein = ein
    val save_lastRead = lastRead
    val save_lastWrite = lastWrite

    try {
      // reset local definitions
      lastRead = Map.empty
      lastWrite = Map.empty
      closure
    } finally {
      // restore environment
      ein = save_ein
      lastRead = save_lastRead
      lastWrite = save_lastWrite
    }
  }
}

class Frontend {

  val g = new GraphBuilder

  def EmptyEffect = EffectSummary(Set(), Set(), Set(), Set())
  def ReadEffect(x: Exp) = EffectSummary(Set(), Set(x), Set(), Set())
  def WriteEffect(x: Exp) = EffectSummary(Set(), Set(), Set(x), Set())
  def ReadWriteEffect(x: Exp) = EffectSummary(Set(), Set(x), Set(x), Set())

  // user-accessible functions

  def getGraph(f: Exp => Exp) = {
    val block = g.reify(f)
    Graph(g.globalDefs.toList, block)
  }

  // program constructs

  type Rep[T] = Exp

  implicit def lift(x: Any) = {
    g.reflect("", Const(x))(Set(), false)(EmptyEffect)
  }

  def print(io: Exp, x: Exp) = {
    g.reflect("print", io, x)(Set(), false)(ReadWriteEffect(io))
  }

  def alloc(x: Exp) = {
    g.reflect("alloc", x)(Set(), true)(ReadEffect(x), true)
  }

  def get(x: Exp) = {
    g.reflect("get", x)(Set(), false)(ReadEffect(x))
  }

  def set(x: Exp, v: Exp) = {
    g.reflect("set", x, v)(Set(), false)(WriteEffect(x))
  }
}
