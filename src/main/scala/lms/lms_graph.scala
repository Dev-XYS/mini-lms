package lms

import collection.mutable
import java.io._

object Backend {

  abstract class Def {}
  abstract class Exp extends Def

  case class Sym(n: Int) extends Exp {
    override def toString = s"x$n"
  }
  case class Const(x: Any) extends Exp {
    override def toString = x.toString
  }

  abstract class Alias {
    def excluding(keys: Set[Exp]): Alias

    def tracked: Boolean

    def ++(keys: Set[Exp]): Alias

    def contains(key: Exp): Boolean

    def subst(from: Exp, to: Exp): Alias

    def aliasSet: Set[Exp]
  }

  case object Untracked extends Alias {
    override def toString = ""

    def excluding(keys: Set[Exp]) = Untracked

    def tracked = false

    def ++(keys: Set[Exp]) = Untracked

    def contains(key: Exp) = false

    def subst(from: Exp, to: Exp) = Untracked

    def aliasSet = Set.empty
  }

  case class Tracked(aliases: Set[Exp]) extends Alias {
    override def toString = s"^{${aliases.mkString(" ")}}"

    def excluding(keys: Set[Exp]) = {
      Tracked(aliases -- keys)
    }

    def tracked = true

    def ++(keys: Set[Exp]) = {
      Tracked(aliases ++ keys)
    }

    def contains(key: Exp) = {
      aliases.contains(key)
    }

    def subst(from: Exp, to: Exp) = {
      Tracked(aliases map (x => if (x == from) to else x))
    }

    def aliasSet = aliases
  }

  abstract class Type(val alias: Alias) {
    def withNewAlias(alias: Alias): Type

    def excludeKeys(keys: Set[Exp]): Type

    def tracked = alias.tracked

    def withAdditionalAlias(keys: Set[Exp]): Type

    def substAlias(from: Exp, to: Exp): Type
  }

  case class TyValue(override val alias: Alias) extends Type(alias) {
    override def toString = {
      s"#$alias"
    }

    def withNewAlias(alias: Alias) = {
      TyValue(alias)
    }

    def excludeKeys(keys: Set[Exp]) = {
      TyValue(alias excluding keys)
    }

    def withAdditionalAlias(keys: Set[Exp]) = {
      TyValue(alias ++ keys)
    }

    def substAlias(from: Exp, to: Exp) = {
      TyValue(alias.subst(from, to))
    }
  }

  case class TyLambda(funSym: Sym, argSym: Sym, arg: Type, res: Type, override val alias: Alias, eff: EffectSummary) extends Type(alias) {
    override def toString = {
      s"$funSym($argSym:$arg => $res)$alias ^^{ $eff }"
    }

    def withNewAlias(alias: Alias) = {
      TyLambda(funSym, argSym, arg, res, alias, eff)
    }

    def excludeKeys(keys: Set[Exp]) = {
      TyLambda(funSym, argSym, arg excludeKeys (keys - funSym - argSym), res excludeKeys (keys - funSym - argSym), alias excluding keys, eff excluding keys)
    }

    def withAdditionalAlias(keys: Set[Exp]) = {
      TyLambda(funSym, argSym, arg, res, alias ++ keys, eff)
    }

    def substAlias(from: Exp, to: Exp) = {
      TyLambda(funSym, argSym, arg, res, alias.subst(from, to), eff)
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

  case class Block(in: List[Sym], res: Exp, ein: Sym, eff: EffectSummary, deps: Dependency, used: Set[Exp], defined: Set[Exp]) extends Def {
    override def toString = s"Block(in: [${in.mkString(" ")}], result: $res, effect: { $eff }, deps: { $deps })"
  }

  case class Dependency(hdeps: Map[Exp, Set[Exp]], sdeps: Map[Exp, Set[Exp]]) {
    override def toString = s"hard: {${hdeps.mkString(" ")}}, soft: {${sdeps.mkString(" ")}}"
  }

  object Dependency {
    def fromMutable(hdeps: mutable.Map[Exp, mutable.Set[Exp]], sdeps: mutable.Map[Exp, mutable.Set[Exp]]) = {
      Dependency(Map(hdeps.toSeq.map({ case (k, v) => (k, Set(v.toSeq: _*)) }): _*), Map(sdeps.toSeq.map({ case (k, v) => (k, Set(v.toSeq: _*)) }): _*))
    }
  }

  case class EffectSummary(init: Set[Exp], read: Set[Exp], write: Set[Exp], kill: Set[Exp]) {
    override def toString = s"init: [${init.mkString(" ")}], read: [${read.mkString(" ")}], write: [${write.mkString(" ")}], kill: [${kill.mkString(" ")}]"

    def mergeWith(eff: EffectSummary) =
      EffectSummary(
        init
          ++ eff.init
          -- eff.write // write overrides init
          -- eff.kill // kill overrides init
        ,
        read
          ++ eff.read
          -- eff.write // write overrides read (if a location is written to, we do not care if it is read)
          -- eff.kill // kill overrides read
        ,
        write
          ++ eff.write
          -- eff.kill // kill overrides write
        ,
        kill
          ++ eff.kill
      )

    def +(eff: EffectSummary) = EffectSummary(init ++ eff.init, read ++ eff.read, write ++ eff.write, kill ++ eff.kill)

    def excluding(keys: Set[Exp]) = {
      EffectSummary(init -- keys, read -- keys, write -- keys, kill -- keys)
    }

    def isEmpty: Boolean = init.isEmpty && read.isEmpty && write.isEmpty && kill.isEmpty

    def subst(from: Exp, to: Exp) = {
      EffectSummary(
        init map (x => if (x == from) to else x),
        read map (x => if (x == from) to else x),
        write map (x => if (x == from) to else x),
        kill map (x => if (x == from) to else x)
      )
    }
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

  var localUsed = mutable.Set[Exp]()
  var localDefined = mutable.Set[Exp]()

  var initSym = mutable.Map[Exp, Exp]()
  var lastRead = mutable.Map[Exp, mutable.Set[Exp]]()
  var lastWrite = mutable.Map[Exp, Exp]()
  var killAt = mutable.Map[Exp, Exp]()

  // end local definitions

  var nSyms = 0
  def fresh = try nSyms
  finally nSyms += 1

  def freshSym = Sym(fresh)

  def reflect(s: Sym, op: String, as: Def*)(ty: Type)(used: Set[Exp])(eff: EffectSummary) = {
    // compute dependencies

    val hdeps = mutable.Map[Exp, mutable.Set[Exp]]()
    val sdeps = mutable.Map[Exp, mutable.Set[Exp]]()

    // compute aliases: all aliases have the same effect
    val init = transitiveAlias(eff.init)
    val read = transitiveAlias(eff.read)
    val write = transitiveAlias(eff.write)
    val kill = transitiveAlias(eff.kill)

    // update local effects
    localEffects = localEffects.mergeWith(EffectSummary(init, read, write, kill))

    // update dependencies and states
    for (i <- init) {
      initSym(i) = i
    }

    for (r <- read) {
      hdeps.getOrElseUpdate(r, mutable.Set()) += lastWriteOrInit(r)
      lastRead.getOrElseUpdate(r, mutable.Set()) += s
    }

    for (w <- write) {
      sdeps.getOrElseUpdate(w, mutable.Set()) += lastWriteOrInit(w)
      sdeps(w) ++= lastRead.getOrElse(w, mutable.Set()) - s
      lastWrite(w) = s
      lastRead(w) = mutable.Set()
    }

    for (k <- kill) {
      sdeps.getOrElseUpdate(k, mutable.Set()) += lastWriteOrInit(k)
      sdeps(k) ++= lastRead.getOrElse(k, mutable.Set()) - s
      killAt(k) = s
      lastWrite remove k
      lastRead(k) = mutable.Set()
    }

    // construct node
    val node = Node(s, op, as.toList, ty, Dependency.fromMutable(hdeps, sdeps))
    globalDefs += node

    // update `localUsed` and `localDefined`
    localUsed ++= used
    localDefined += s

    s
  }

  def reify(f: Exp => Exp) = withScope {
    // generate symbolic argument
    val x = freshSym

    // set current `ein` (for now, it is the same as the function argument)
    ein = x

    // execute the function
    val res = f(x)

    // The returned value is also used.
    localUsed += res

    // compute dependencies for the whole block

    val hdeps = mutable.Map[Exp, mutable.Set[Exp]]()
    val sdeps = mutable.Map[Exp, mutable.Set[Exp]]()

    for ((key, rs) <- lastRead) {
      sdeps(key) = rs
    }

    for ((key, w) <- lastWrite) {
      // Local effects are soft dependencies and non-local effects are hard dependencies.
      if (localDefined contains key)
        sdeps.getOrElseUpdate(key, mutable.Set()) += w
      else
        hdeps.getOrElseUpdate(key, mutable.Set()) += w
    }

    for ((key, k) <- killAt) {
      if (localDefined contains key)
        sdeps.getOrElseUpdate(key, mutable.Set()) += k
      else
        hdeps.getOrElseUpdate(key, mutable.Set()) += k
    }

    // return a block
    Block(List(x), res, x, localEffects, Dependency.fromMutable(hdeps, sdeps), Set(localUsed.toSeq: _*), Set(localDefined.toSeq: _*))
  }

  def lastWriteOrInit(x: Exp) = {
    lastWrite.getOrElse(x, initSym.getOrElse(x, ein))
  }

  def withScope(closure: => Block) = {
    // scoping: save the current environment
    val save_ein = ein
    val save_localEffects = localEffects
    val save_localUsed = localUsed
    val save_localDefined = localDefined
    val save_initSym = initSym
    val save_lastRead = lastRead
    val save_lastWrite = lastWrite
    val save_killAt = killAt

    try {
      // reset local definitions
      localEffects = EmptyEffect
      localUsed = mutable.Set.empty
      localDefined = mutable.Set.empty
      initSym = mutable.Map.empty
      lastRead = mutable.Map.empty
      lastWrite = mutable.Map.empty
      killAt = mutable.Map.empty
      closure
    } finally {
      // restore environment
      ein = save_ein
      localEffects = save_localEffects
      localUsed = save_localUsed
      localDefined = save_localDefined
      initSym = save_initSym
      lastRead = save_lastRead
      lastWrite = save_lastWrite
      killAt = save_killAt
    }
  }

  def getNode(s: Sym): Option[Node] = {
    globalDefs.find(_.s == s)
  }

  def transitiveAlias(aliases: Set[Exp]): Set[Exp] = {
    val res = mutable.Set[Exp]()
    def helper(set: Set[Exp]) {
      for (x <- set) {
        if (x.isInstanceOf[Sym]) {
          val s = x.asInstanceOf[Sym]
          if (!(res contains s)) {
            res += s
            val _node = getNode(s)
            _node match {
              case Some(node) => helper(node.ty.alias.aliasSet)
              case _          =>
            }
          }
        }
      }
    }
    helper(aliases)
    Set(res.toSeq: _*)
  }
}

class Frontend {

  val g = new GraphBuilder

  def InitEffect(x: Exp) = EffectSummary(Set(x), Set(), Set(), Set())
  def ReadEffect(x: Exp) = EffectSummary(Set(), Set(x), Set(), Set())
  def WriteEffect(x: Exp) = EffectSummary(Set(), Set(), Set(x), Set())
  def ReadWriteEffect(x: Exp) = EffectSummary(Set(), Set(x), Set(x), Set())
  def KillEffect(x: Exp) = EffectSummary(Set(), Set(), Set(), Set(x))

  // user-accessible functions

  def getGraph(f: Exp => Exp) = {
    val block = g.reify(f)
    Graph(g.globalDefs.toList, block)
  }

  // program constructs

  type Rep[T] = Exp

  implicit def lift(x: Any) = {
    val s = g.freshSym
    g.reflect(s, "", Const(x))(TyValue(Untracked))(Set())(EmptyEffect)
  }

  def print(io: Exp, x: Exp) = {
    val s = g.freshSym
    g.reflect(s, "print", io, x)(TyValue(Untracked))(Set(io, x))(ReadWriteEffect(io))
  }

  def alloc(x: Exp) = {
    val s = g.freshSym
    g.reflect(s, "alloc", x)(TyValue(Tracked(Set(s))))(Set(x))(ReadEffect(x) + InitEffect(s))
  }

  def get(x: Exp) = {
    val s = g.freshSym
    g.reflect(s, "get", x)(TyValue(Untracked))(Set(x))(ReadEffect(x))
  }

  def set(x: Exp, v: Exp) = {
    val s = g.freshSym
    g.reflect(s, "set", x, v)(TyValue(Untracked))(Set(x, v))(WriteEffect(x))
  }

  def inc(x: Exp) = {
    val s = g.freshSym
    g.reflect(s, "inc", x)(TyValue(Untracked))(Set(x))(ReadWriteEffect(x))
  }

  def free(x: Exp) = {
    val s = g.freshSym
    g.reflect(s, "free", x)(TyValue(Untracked))(Set(x))(KillEffect(x))
  }

  def fun(f: Exp => Exp) = {
    val s = g.freshSym
    val block = g.reify(f)
    val tyRes = g.getNode(block.res.asInstanceOf[Sym]).get.ty

    // rewire escaping closures
    val tyResRewired =
      (tyRes match {
        case TyLambda(funSym, argSym, arg, res, alias, eff) => {
          res.alias match {
            case Tracked(aliases) => {
              val _aliases =
                if (aliases exists (x => block.defined contains x)) {
                  // closure escaped
                  aliases + block.res
                } else {
                  aliases
                }
              TyLambda(funSym, argSym, arg, res.withNewAlias(Tracked(_aliases -- (block.defined - funSym))), alias, eff)
            }
            case _ => tyRes
          }
        }
        case _ => tyRes
      })
        // eliminate unavailable variables
        .excludeKeys(block.defined)

    val lamEff = block.eff excluding block.defined
    val usedNonlocal = block.used -- block.defined -- block.in.toSet

    g.reflect(s, "λ", block)(
      // assume that lambda has exactly one parameter
      TyLambda(
        s,
        block.in(0),
        TyValue(Tracked(Set())),
        tyResRewired,
        Tracked(usedNonlocal ++ (if (usedNonlocal.isEmpty) Set() else Set(s))),
        lamEff
      )
    )(Set())(if ((lamEff excluding block.in.toSet).isEmpty) EmptyEffect else InitEffect(s) /* If a function closes over something, it has an init effect. (not sure) */ )
  }

  implicit class Lambda(f: Exp) {
    def apply(x: Exp) = {
      val s = g.freshSym
      val node = g.getNode(f.asInstanceOf[Sym]).get
      val ty = node.ty.asInstanceOf[TyLambda]

      // The function is in the form f(x:#) => #^{f}.
      // replace `f` in the alias set of result with the function symbol (not sure)
      val _tyRes =
        if (ty.res.alias.contains(ty.funSym)) ty.res.substAlias(ty.funSym, f)
        else ty.res

      // The function is in the form f(x:#) => #^{x}.
      // replace `x` in the alias set of result with the argument symbol
      val tyRes =
        if (_tyRes.alias.contains(ty.argSym)) _tyRes.substAlias(ty.argSym, x)
        else _tyRes

      // The function is in the form f(x:#) => # ^^{x}
      val appEff = ty.eff.subst(ty.argSym, x)

      // Tracked result is initialized.
      val eff =
        if (tyRes.tracked) appEff + InitEffect(s)
        else appEff

      // reflect
      // (If an application returns a tracked value, it must at least alias itself. Not sure.)
      g.reflect(s, "@", f, x)(if (tyRes.tracked) tyRes.withAdditionalAlias(Set(s)) else tyRes)(Set(f))(eff)
    }
  }
}
