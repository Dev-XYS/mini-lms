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

  abstract class Aliases

  case object Untracked extends Aliases {
    override def toString = ""
  }
  case class Tracked(aliases: Set[Exp]) extends Aliases {
    override def toString = s"^{${aliases.mkString(" ")}}"
  }

  abstract class Type(val aliases: Aliases) {}

  case class TyValue(override val aliases: Aliases) extends Type(aliases) {
    override def toString = {
      s"#$aliases"
    }
  }
  case class TyLambda(arg: Type, res: Type, override val aliases: Aliases, eff: EffectSummary) extends Type(aliases) {
    override def toString = {
      s"($arg => $res)$aliases ^^{ $eff }"
    }
  }

  case class Node(s: Sym, op: String, rhs: List[Def], ty: Type, deps: Dependency) {
    override def toString =
      if (op == "")
        // constant
        s"$s = ${rhs.mkString(" ")}, type: $ty"
      else
        // non-constant
        s"$s = $op(${rhs.mkString(" ")}), type: $ty, deps: { $deps }"
  }

  case class Block(in: List[Sym], res: Exp, ein: Sym, eff: EffectSummary, deps: Dependency) extends Def {
    override def toString = s"in: [${in.mkString(" ")}], result: $res, effect: { $eff }, deps: { $deps }"
  }

  case class Dependency(hdeps: Map[Exp, Set[Exp]], sdeps: Map[Exp, Set[Exp]]) {
    override def toString = s"hard: {${hdeps.mkString(" ")}}, soft: {${sdeps.mkString(" ")}}"
  }

  case class EffectSummary(init: Set[Exp], read: Set[Exp], write: Set[Exp], kill: Set[Exp]) {
    override def toString = s"init: [${init.mkString(" ")}], read: [${read.mkString(" ")}], write: [${write.mkString(" ")}], kill: [${kill.mkString(" ")}]"

    def mergeWith(eff: EffectSummary) {
      init ++= eff.init
      read ++= eff.read
      write ++= eff.write
      kill ++= eff.kill
    }

    def +(eff: EffectSummary) = EffectSummary(init ++ eff.init, read ++ eff.read, write ++ eff.write, kill ++ eff.kill)
  }

  def EmptyEffect = EffectSummary(Set(), Set(), Set(), Set())

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

  var ein = Sym(-1)

  var localEffects: EffectSummary = EmptyEffect

  var initSym = Map[Exp, Exp]()
  var lastRead = Map[Exp, Set[Exp]]()
  var lastWrite = Map[Exp, Exp]()

  // end local definitions

  var nSyms = 0
  def fresh = try nSyms
  finally nSyms += 1

  def freshSym = Sym(fresh)

  def reflect(s: Sym, op: String, as: Def*)(ty: Type)(eff: EffectSummary) = {
    // compute dependencies

    val hdeps = Map[Exp, Set[Exp]]()
    val sdeps = Map[Exp, Set[Exp]]()

    // update local effects
    localEffects.mergeWith(eff)

    // update dependencies and states
    // if (init) initSym(s) = s

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
    val node = Node(s, op, as.toList, ty, Dependency(hdeps, sdeps))
    globalDefs += node
    s
  }

  def reify(f: Exp => Exp) = withScope {
    // generate symbolic argument
    val x = freshSym

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
    Block(List(x), res, x, localEffects, Dependency(hdeps, sdeps))
  }

  def lastWriteOrInit(x: Exp) = {
    lastWrite.getOrElse(x, initSym.getOrElse(x, ein))
  }

  def withScope(closure: => Block) = {
    // scoping: save the current environment
    val save_ein = ein
    val save_localEffects = localEffects
    val save_lastRead = lastRead
    val save_lastWrite = lastWrite

    try {
      // reset local definitions
      localEffects = EmptyEffect
      lastRead = Map.empty
      lastWrite = Map.empty
      closure
    } finally {
      // restore environment
      ein = save_ein
      localEffects = save_localEffects
      lastRead = save_lastRead
      lastWrite = save_lastWrite
    }
  }

  def getNode(s: Sym): Node = {
    val Some(node) = globalDefs.find(_.s == s)
    node
  }
}

class Frontend {

  val g = new GraphBuilder

  def InitEffect(x: Exp) = EffectSummary(Set(x), Set(), Set(), Set())
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
    val s = g.freshSym
    g.reflect(s, "", Const(x))(TyValue(Untracked))(EmptyEffect)
  }

  def print(io: Exp, x: Exp) = {
    val s = g.freshSym
    g.reflect(s, "print", io, x)(TyValue(Untracked))(ReadWriteEffect(io))
  }

  def alloc(x: Exp) = {
    val s = g.freshSym
    g.reflect(s, "alloc", x)(TyValue(Tracked(Set(s))))(ReadEffect(x) + InitEffect(s))
  }

  def get(x: Exp) = {
    val s = g.freshSym
    g.reflect(s, "get", x)(TyValue(Untracked))(ReadEffect(x))
  }

  def set(x: Exp, v: Exp) = {
    val s = g.freshSym
    g.reflect(s, "set", x, v)(TyValue(Untracked))(WriteEffect(x))
  }

  def inc(x: Exp) = {
    val s = g.freshSym
    g.reflect(s, "inc", x)(TyValue(Untracked))(ReadWriteEffect(x))
  }

  def fun(f: Exp => Exp) = {
    val s = g.freshSym
    val block = g.reify(f)
    val tyRes = g.getNode(block.res.asInstanceOf[Sym]).ty
    g.reflect(s, "λ", block)(TyLambda(TyValue(Tracked(Set())), tyRes, Tracked(Set()), block.eff))(EmptyEffect)
  }

  implicit class Lambda(f: Exp) {
    def apply(x: Exp) = {
      val s = g.freshSym
      val node = g.getNode(f.asInstanceOf[Sym])
      val ty = node.ty.asInstanceOf[TyLambda]
      g.reflect(s, "@", f, x)(ty.res)(ty.eff)
    }
  }
}
