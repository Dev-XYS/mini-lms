package lms

import collection.mutable
import java.io._

object Backend {

  abstract class Def {}
  abstract class Exp extends Def with Ordered[Exp] {
    def compare(that: Exp) = {
      orderingExp.compare(this, that)
    }
  }

  case class Sym(n: Int) extends Exp {
    override def toString =
      if (n < 0) s"x{$n}"
      else s"x$n"

    def isFunLevel = n < 0 && (n & 1) == 1
    def isArgLevel = n < 0 && (n & 1) == 0
  }
  case class Const(x: Any) extends Exp {
    override def toString = x.toString
  }

  // order symbols by the size of scope (de Bruijn levels)
  implicit val orderingExp: Ordering[Exp] = Ordering.by(e =>
    e match {
      case s: Sym => if (s.isFunLevel) -s.n else 0
      case _      => 0
    }
  )

  def qualifierSetCompareLte(s1: Set[Exp], s2: Set[Exp]) = {
    if (s1.isEmpty) true
    else {
      if (s2.isEmpty) false
      else {
        s1.max <= s2.max &&
        ((s2.max.asInstanceOf[Sym].isFunLevel) ||
          (s1.filter(!_.asInstanceOf[Sym].isFunLevel) subsetOf s2.filter(!_.asInstanceOf[Sym].isFunLevel)))
      }
    }
  }

  abstract class Alias {
    def excluding(keys: Set[Exp]): Alias

    def tracked: Boolean

    def ++(keys: Set[Exp]): Alias

    def contains(key: Exp): Boolean

    def subst(from: Exp, to: Exp): Alias

    def aliasSet: Set[Exp]

    def <=(rhs: Alias): Boolean

    def intersectWith(a: Alias): Alias
  }

  case object Untracked extends Alias {
    override def toString = ""

    def excluding(keys: Set[Exp]) = Untracked

    def tracked = false

    def ++(keys: Set[Exp]) = Untracked

    def contains(key: Exp) = false

    def subst(from: Exp, to: Exp) = Untracked

    def aliasSet = Set.empty

    def <=(rhs: Alias) = true

    def intersectWith(a: Alias) = Untracked
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

    def <=(rhs: Alias): Boolean = {
      if (rhs == Untracked) return false
      val _aliases = rhs.asInstanceOf[Tracked].aliases
      qualifierSetCompareLte(aliases, _aliases)
    }

    def intersectWith(a: Alias) = {
      if (a == Untracked) {
        Untracked
      } else {
        val Tracked(as) = a
        Tracked(aliases intersect as)
      }
    }
  }

  abstract class Type(val alias: Alias) {
    def withNewAlias(alias: Alias): Type

    def excludeKeys(keys: Set[Exp]): Type

    def tracked = alias.tracked

    def withAdditionalAlias(keys: Set[Exp]): Type

    def substAlias(from: Exp, to: Exp): Type

    def subst(from: Exp, to: Exp): Type

    def isSubtypeOf(ty: Type): Boolean

    def intersectAliasWith(a: Alias): Type
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

    def subst(from: Exp, to: Exp) = {
      TyValue(alias.subst(from, to))
    }

    def isSubtypeOf(ty: Type) = {
      ty.isInstanceOf[TyValue] && (alias <= ty.alias)
    }

    def intersectAliasWith(a: Alias) = {
      TyValue(alias intersectWith a)
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
      TyLambda(funSym, argSym, arg excludeKeys (keys - funSym - argSym), res excludeKeys (keys - funSym - argSym), alias excluding keys, eff excluding (keys - funSym - argSym))
    }

    def withAdditionalAlias(keys: Set[Exp]) = {
      TyLambda(funSym, argSym, arg, res, alias ++ keys, eff)
    }

    def substAlias(from: Exp, to: Exp) = {
      TyLambda(funSym, argSym, arg, res, alias.subst(from, to), eff)
    }

    def subst(from: Exp, to: Exp) = {
      TyLambda(funSym, argSym, arg, res.subst(from, to), alias.subst(from, to), eff.subst(from, to))
    }

    def isSubtypeOf(ty: Type): Boolean = {
      if (!(alias <= ty.alias)) return false
      if (ty.isInstanceOf[TyValue]) return true
      val lam = ty.asInstanceOf[TyLambda]
      (lam.arg isSubtypeOf arg) && (res isSubtypeOf lam.res) && (eff <= lam.eff)
    }

    def intersectAliasWith(a: Alias) = {
      TyLambda(funSym, argSym, arg, res, alias intersectWith a, eff)
    }
  }

  // convert a type to its (reversed) de Bruijn representation (for self references in subtype checking)
  def toDeBruijn(ty: Type) = {
    def helper(ty: Type, lv: Int): Type = {
      ty match {
        case TyValue(alias) => TyValue(alias)
        case TyLambda(funSym, argSym, arg, res, alias, eff) =>
          TyLambda(
            funSym,
            argSym,
            helper(arg, lv - 1),
            helper(res.subst(funSym, Sym(lv * 2 + 1)).subst(argSym, Sym(lv * 2)), lv - 1),
            alias.subst(funSym, Sym(lv * 2 + 1)).subst(argSym, Sym(lv * 2)),
            eff.subst(funSym, Sym(lv * 2 + 1)).subst(argSym, Sym(lv * 2))
          )
      }
    }
    helper(ty, -1)
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
          ++ (eff.read -- write) // If a key has already been written to, read has no global effect on it.
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

    def <=(eff: EffectSummary) = {
      qualifierSetCompareLte(init, eff.init) &&
      qualifierSetCompareLte(read, eff.read) &&
      qualifierSetCompareLte(write, eff.write) &&
      qualifierSetCompareLte(kill, eff.kill)
    }
  }

  def EmptyEffect = EffectSummary(Set(), Set(), Set(), Set())

  case class Graph(nodes: List[Node], block: Block) {
    override def toString = {
      val source = new java.io.ByteArrayOutputStream()
      val stream = new java.io.PrintStream(source)
      stream.println("====================")
      for (node <- nodes)
        if (node.op != "(arg)") // symbolic arguments should not be printed
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

    // compute dependencies
    for (r <- read) {
      hdeps.getOrElseUpdate(r, mutable.Set()) += lastWriteOrInit(r)
    }

    for (w <- write) {
      sdeps.getOrElseUpdate(w, mutable.Set()) += lastWriteOrInit(w)
      sdeps(w) ++= lastRead.getOrElse(w, mutable.Set())
    }

    for (k <- kill) {
      sdeps.getOrElseUpdate(k, mutable.Set()) += lastWriteOrInit(k)
      sdeps(k) ++= lastRead.getOrElse(k, mutable.Set())
    }

    // update states
    for (i <- init) {
      initSym(i) = i
    }

    for (r <- read) {
      lastRead.getOrElseUpdate(r, mutable.Set()) += s
    }

    for (w <- write) {
      lastWrite(w) = s
      lastRead(w) = mutable.Set()
    }

    for (k <- kill) {
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

  def reify(f: Exp => Exp, x: Sym, tyArg: Type) = withScope {
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

  /* *
   * Calculate the result type when leaving a scope.
   * (Rewiring, eliminating local symbols, ...)
   * */
  def leavingScope(ty: Type, locals: Set[Exp]) = {
    (ty match {
      case TyLambda(funSym, argSym, arg, res, alias, eff) => {
        locals
          .foldLeft(ty)((t, s) => t.subst(s, funSym))
      }
      case _ => ty
    })
      .excludeKeys(locals)
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
    val x = g.freshSym // always assume one tracked argument for now
    val block = g.reify(f, x, TyValue(Tracked(Set(x))))
    Graph(g.globalDefs.toList, block)
  }

  // program constructs

  type Rep = Exp

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

  // begin type annotations

  case class RefFun(lv: Int) extends Exp
  case class RefArg(lv: Int) extends Exp

  abstract class FrontendAlias {
    def substFun(lv: Int, to: Exp): FrontendAlias
    def substArg(lv: Int, to: Exp): FrontendAlias

    def convert: Alias
  }

  case object FrontendUntracked extends FrontendAlias {
    def substFun(lv: Int, to: Exp) = FrontendUntracked
    def substArg(lv: Int, to: Exp) = FrontendUntracked

    def convert = Untracked
  }

  case class FrontendTracked(aliases: Set[Exp]) extends FrontendAlias {
    def substFun(lv: Int, to: Exp) = {
      FrontendTracked(aliases map (x => if (x == RefFun(lv)) to else x))
    }
    def substArg(lv: Int, to: Exp) = {
      FrontendTracked(aliases map (x => if (x == RefArg(lv)) to else x))
    }

    def convert = Tracked(aliases)
  }

  case class FrontendEffect(init: Set[Exp], read: Set[Exp], write: Set[Exp], kill: Set[Exp]) {
    def substFun(lv: Int, to: Exp) = {
      FrontendEffect(
        init map (x => if (x == RefFun(lv)) to else x),
        read map (x => if (x == RefFun(lv)) to else x),
        write map (x => if (x == RefFun(lv)) to else x),
        kill map (x => if (x == RefFun(lv)) to else x)
      )
    }
    def substArg(lv: Int, to: Exp) = {
      FrontendEffect(
        init map (x => if (x == RefArg(lv)) to else x),
        read map (x => if (x == RefArg(lv)) to else x),
        write map (x => if (x == RefArg(lv)) to else x),
        kill map (x => if (x == RefArg(lv)) to else x)
      )
    }

    def convert = {
      EffectSummary(init, read, write, kill)
    }
  }

  val emptyEffect = FrontendEffect(Set(), Set(), Set(), Set())

  abstract class FrontendType {
    def substFun(lv: Int, to: Exp): FrontendType
    def substArg(lv: Int, to: Exp): FrontendType
  }

  case class FrontendValue(alias: FrontendAlias) extends FrontendType {
    def substFun(lv: Int, to: Exp) = {
      FrontendValue(alias.substFun(lv, to))
    }
    def substArg(lv: Int, to: Exp) = {
      FrontendValue(alias.substArg(lv, to))
    }
  }
  case class FrontendLambda(arg: FrontendType, res: FrontendType, alias: FrontendAlias, eff: FrontendEffect) extends FrontendType {
    def substFun(lv: Int, to: Exp) = {
      FrontendLambda(arg.substFun(lv + 1, to), res.substFun(lv + 1, to), alias.substFun(lv, to), eff.substFun(lv, to))
    }
    def substArg(lv: Int, to: Exp) = {
      FrontendLambda(arg.substArg(lv + 1, to), res.substArg(lv + 1, to), alias.substArg(lv, to), eff.substArg(lv, to))
    }
  }

  val uv = FrontendValue(FrontendUntracked)
  val tv = FrontendValue(FrontendTracked(Set.empty))
  val rwk = FrontendLambda(uv, uv, FrontendTracked(Set(RefFun(0))), FrontendEffect(Set(), Set(RefFun(0)), Set(RefFun(0)), Set(RefFun(0))))

  def convertType(ty: FrontendType): Type = {
    def helper(ty: FrontendType): Type = {
      ty match {
        case FrontendValue(alias) => TyValue(alias.convert)
        case FrontendLambda(arg, res, alias, eff) => {
          val funSym = g.freshSym
          val argSym = g.freshSym

          val _arg = helper(arg.substFun(0, funSym).substArg(0, argSym))
          val _res = helper(res.substFun(0, funSym).substArg(0, argSym))
          val _alias = alias.substFun(0, funSym).substArg(0, argSym).convert
          val _eff = eff.substFun(0, funSym).substArg(0, argSym).convert

          // add the argument to the node list for later use
          // not sure if it is the best way to implement it
          g.globalDefs += Node(argSym, "(arg)", List(), _arg, Dependency(Map(), Map()))

          TyLambda(funSym, argSym, _arg, _res, _alias, _eff)
        }
      }
    }

    helper(ty)
  }

  // end type annotations

  def fun(_tyArg: FrontendType = tv)(f: Exp => Exp) = {
    val s = g.freshSym
    val x = g.freshSym // symbol for the argument

    val tyArg = convertType(_tyArg)

    // add dummy argument to node list
    g.globalDefs += Node(x, "(arg)", List(), tyArg, Dependency(Map(), Map()))

    val block = g.reify(f, x, tyArg)
    val tyRes = g.getNode(block.res.asInstanceOf[Sym]).get.ty

    val tyResRewired = g.leavingScope(tyRes, block.defined)

    val lamEff = block.eff excluding block.defined
    val usedNonlocal = block.used -- block.defined -- block.in.toSet

    g.reflect(s, "λ", block)(
      // assume that lambda has exactly one parameter
      TyLambda(
        s,
        block.in(0),
        tyArg,
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

      val actualType = toDeBruijn(g.getNode(x.asInstanceOf[Sym]).get.ty).intersectAliasWith(node.ty.alias)
      val requiredType = toDeBruijn(ty.arg)

      if (!(actualType isSubtypeOf requiredType)) {
        println(s"[Type Error]\n  Required (${ty.argSym}): $requiredType\n    Actual ($x): $actualType")
      }

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

      // The function is in the form f(x:#) => # ^^{f}
      val _appEff = ty.eff.subst(ty.funSym, f)

      // The function is in the form f(x:#) => # ^^{x}
      val appEff = _appEff.subst(ty.argSym, x)

      // Tracked result is initialized.
      val eff =
        if (tyRes.tracked) appEff + InitEffect(s)
        else appEff

      // reflect
      // (If an application returns a tracked value, it must at least alias itself.)
      g.reflect(s, "@", f, x)(if (tyRes.tracked) tyRes.withAdditionalAlias(Set(s)) else tyRes)(Set(f))(eff)
    }
  }
}
