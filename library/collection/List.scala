/* Copyright 2009-2015 EPFL, Lausanne */

package leon.collection

import leon._
import leon.lang._
import leon.annotation._
import leon.math._
import leon.proof._

@library
sealed abstract class List[T] {

  def size: BigInt = (this match {
    case Nil() => BigInt(0)
    case Cons(h, t) => 1 + t.size
  }) ensuring (_ >= 0)

  def content: Set[T] = this match {
    case Nil() => Set()
    case Cons(h, t) => Set(h) ++ t.content
  }

  def contains(v: T): Boolean = (this match {
    case Cons(h, t) if h == v => true
    case Cons(_, t) => t.contains(v)
    case Nil() => false
  }) ensuring { _ == (content contains v) }

  def ++(that: List[T]): List[T] = (this match {
    case Nil() => that
    case Cons(x, xs) => Cons(x, xs ++ that)
  }) ensuring { res =>
    (res.content == this.content ++ that.content) &&
    (res.size == this.size + that.size)
  }

  def head: T = {
    require(this != Nil[T]())
    val Cons(h, _) = this
    h
  }

  def tail: List[T] = {
    require(this != Nil[T]())
    val Cons(_, t) = this
    t
  }

  def apply(index: BigInt): T = {
    require(0 <= index && index < size)
    if (index == BigInt(0)) {
      head
    } else {
      tail(index-1)
    }
  }

  def ::(t:T): List[T] = Cons(t, this)

  def :+(t:T): List[T] = {
    this match {
      case Nil() => Cons(t, this)
      case Cons(x, xs) => Cons(x, xs :+ (t))
    }
  } ensuring(res => (res.size == size + 1) && (res.content == content ++ Set(t)))

  def reverse: List[T] = {
    this match {
      case Nil() => this
      case Cons(x,xs) => xs.reverse :+ x
    }
  } ensuring (res => (res.size == size) && (res.content == content))

  def take(i: BigInt): List[T] = { (this, i) match {
    case (Nil(), _) => Nil[T]()
    case (Cons(h, t), i) =>
      if (i <= BigInt(0)) {
        Nil[T]()
      } else {
        Cons(h, t.take(i-1))
      }
  }} ensuring { res =>
    res.content.subsetOf(this.content) && (res.size == (
      if      (i <= 0)         BigInt(0)
      else if (i >= this.size) this.size
      else                     i
    ))
  }

  def drop(i: BigInt): List[T] = { (this, i) match {
    case (Nil(), _) => Nil[T]()
    case (Cons(h, t), i) =>
      if (i <= BigInt(0)) {
        Cons[T](h, t)
      } else {
        t.drop(i-1)
      }
  }} ensuring { res =>
    res.content.subsetOf(this.content) && (res.size == (
      if      (i <= 0)         this.size
      else if (i >= this.size) BigInt(0)
      else                     this.size - i
    ))
  }

  def slice(from: BigInt, to: BigInt): List[T] = {
    require(0 <= from && from <= to && to <= size)
    drop(from).take(to-from)
  }

  def replace(from: T, to: T): List[T] = { this match {
    case Nil() => Nil[T]()
    case Cons(h, t) =>
      val r = t.replace(from, to)
      if (h == from) {
        Cons(to, r)
      } else {
        Cons(h, r)
      }
  }} ensuring { (res: List[T]) =>
    res.size == this.size &&
    res.content == (
      (this.content -- Set(from)) ++
      (if (this.content contains from) Set(to) else Set[T]())
    )
  }

  private def chunk0(s: BigInt, l: List[T], acc: List[T], res: List[List[T]], s0: BigInt): List[List[T]] = l match {
    case Nil() =>
      if (acc.size > 0) {
        res :+ acc
      } else {
        res
      }
    case Cons(h, t) =>
      if (s0 == BigInt(0)) {
        chunk0(s, l, Nil(), res :+ acc, s)
      } else {
        chunk0(s, t, acc :+ h, res, s0-1)
      }
  }

  def chunks(s: BigInt): List[List[T]] = {
    require(s > 0)

    chunk0(s, this, Nil(), Nil(), s)
  }

  def zip[B](that: List[B]): List[(T, B)] = { (this, that) match {
    case (Cons(h1, t1), Cons(h2, t2)) =>
      Cons((h1, h2), t1.zip(t2))
    case _ =>
      Nil[(T, B)]()
  }} ensuring { _.size == (
    if (this.size <= that.size) this.size else that.size
  )}

  def -(e: T): List[T] = { this match {
    case Cons(h, t) =>
      if (e == h) {
        t - e
      } else {
        Cons(h, t - e)
      }
    case Nil() =>
      Nil[T]()
  }} ensuring { res =>
    res.size <= this.size &&
    res.content == this.content -- Set(e)
  }

  def --(that: List[T]): List[T] = { this match {
    case Cons(h, t) =>
      if (that.contains(h)) {
        t -- that
      } else {
        Cons(h, t -- that)
      }
    case Nil() =>
      Nil[T]()
  }} ensuring { res =>
    res.size <= this.size &&
    res.content == this.content -- that.content
  }

  def &(that: List[T]): List[T] = { this match {
    case Cons(h, t) =>
      if (that.contains(h)) {
        Cons(h, t & that)
      } else {
        t & that
      }
    case Nil() =>
      Nil[T]()
  }} ensuring { res =>
    res.size <= this.size &&
    res.content == (this.content & that.content)
  }

  def padTo(s: BigInt, e: T): List[T] = { (this, s) match {
    case (_, s) if s <= 0 =>
      this
    case (Nil(), s) =>
      Cons(e, Nil().padTo(s-1, e))
    case (Cons(h, t), s) =>
      Cons(h, t.padTo(s-1, e))
  }} ensuring { res =>
    if (s <= this.size)
      res == this
    else
      res.size == s &&
      res.content == this.content ++ Set(e)
  }

  def find(e: T): Option[BigInt] = { this match {
    case Nil() => None[BigInt]()
    case Cons(h, t) =>
      if (h == e) {
        Some[BigInt](0)
      } else {
        t.find(e) match {
          case None()  => None[BigInt]()
          case Some(i) => Some(i+1)
        }
      }
    }} ensuring { res => !res.isDefined || (this.content contains e) }

  def init: List[T] = {
    require(!isEmpty)
    (this match {
      case Cons(h, Nil()) =>
        Nil[T]()
      case Cons(h, t) =>
        Cons[T](h, t.init)
    })
  } ensuring ( (r: List[T]) =>
    r.size == this.size - 1 &&
    r.content.subsetOf(this.content)
  )

  def last: T = {
    require(!isEmpty)
    this match {
      case Cons(h, Nil()) => h
      case Cons(_, t) => t.last
    }
  } ensuring { this.contains _ }

  def lastOption: Option[T] = { this match {
    case Cons(h, t) =>
      t.lastOption.orElse(Some(h))
    case Nil() =>
      None[T]()
  }} ensuring { _.isDefined != this.isEmpty }

  def firstOption: Option[T] = { this match {
    case Cons(h, t) =>
      Some(h)
    case Nil() =>
      None[T]()
  }} ensuring { _.isDefined != this.isEmpty }

  def unique: List[T] = this match {
    case Nil() => Nil()
    case Cons(h, t) =>
      Cons(h, t.unique - h)
  }

  def splitAt(e: T): List[List[T]] =  split(Cons(e, Nil()))

  def split(seps: List[T]): List[List[T]] = this match {
    case Cons(h, t) =>
      if (seps.contains(h)) {
        Cons(Nil(), t.split(seps))
      } else {
        val r = t.split(seps)
        Cons(Cons(h, r.head), r.tail)
      }
    case Nil() =>
      Cons(Nil(), Nil())
  }

  def evenSplit: (List[T], List[T]) = {
    val c = size/2
    (take(c), drop(c))
  }

  def insertAt(pos: BigInt, l: List[T]): List[T] = {
    if(pos < 0) {
      insertAt(size + pos, l)
    } else if(pos == BigInt(0)) {
      l ++ this
    } else {
      this match {
        case Cons(h, t) =>
          Cons(h, t.insertAt(pos-1, l))
        case Nil() =>
          l
      }
    }
  } ensuring { res =>
    res.size == this.size + l.size &&
    res.content == this.content ++ l.content
  }

  def replaceAt(pos: BigInt, l: List[T]): List[T] = {
    if(pos < 0) {
      replaceAt(size + pos, l)
    } else if(pos == BigInt(0)) {
      l ++ this.drop(l.size)
    } else {
      this match {
        case Cons(h, t) =>
          Cons(h, t.replaceAt(pos-1, l))
        case Nil() =>
          l
      }
    }
  } ensuring { res =>
    res.content.subsetOf(l.content ++ this.content)
  }

  def rotate(s: BigInt): List[T] = {
    if (s < 0) {
      rotate(size + s)
    } else if (s > size) {
      rotate(s - size)
    } else {
      drop(s) ++ take(s)
    }
  } ensuring { res =>
    res.size == this.size
  }

  def isEmpty = this match {
    case Nil() => true
    case _ => false
  }

  // Higher-order API
  def map[R](f: T => R): List[R] = { this match {
    case Nil() => Nil[R]()
    case Cons(h, t) => f(h) :: t.map(f)
  }} ensuring { _.size == this.size }

  def foldLeft[R](z: R)(f: (R,T) => R): R = this match {
    case Nil() => z
    case Cons(h,t) => t.foldLeft(f(z,h))(f)
  }

  def foldRight[R](z: R)(f: (T,R) => R): R = this match {
    case Nil() => z
    case Cons(h, t) => f(h, t.foldRight(z)(f))
  }

  def scanLeft[R](z: R)(f: (R,T) => R): List[R] = { this match {
    case Nil() => z :: Nil()
    case Cons(h,t) => z :: t.scanLeft(f(z,h))(f)
  }} ensuring { !_.isEmpty }

  def scanRight[R](z: R)(f: (T,R) => R): List[R] = { this match {
    case Nil() => z :: Nil[R]()
    case Cons(h, t) =>
      val rest@Cons(h1,_) = t.scanRight(z)(f)
      f(h, h1) :: rest
  }} ensuring { !_.isEmpty }

  def flatMap[R](f: T => List[R]): List[R] =
    ListOps.flatten(this map f)

  def filter(p: T => Boolean): List[T] = { this match {
    case Nil() => Nil[T]()
    case Cons(h, t) if p(h) => Cons(h, t.filter(p))
    case Cons(_, t) => t.filter(p)
  }} ensuring { res =>
    res.size <= this.size &&
    res.content.subsetOf(this.content) &&
    res.forall(p)
  }

  def filterNot(p: T => Boolean): List[T] =
    filter(!p(_)) ensuring { res =>
      res.size <= this.size &&
      res.content.subsetOf(this.content) &&
      res.forall(!p(_))
    }

  def partition(p: T => Boolean): (List[T], List[T]) = { this match {
    case Nil() => (Nil[T](), Nil[T]())
    case Cons(h, t) =>
      val (l1, l2) = t.partition(p)
      if (p(h)) (h :: l1, l2)
      else      (l1, h :: l2)
  }} ensuring { res =>
    res._1 == filter(p) &&
    res._2 == filterNot(p)
  }

  // In case we implement for-comprehensions
  def withFilter(p: T => Boolean) = filter(p)

  def forall(p: T => Boolean): Boolean = this match {
    case Nil() => true
    case Cons(h, t) => p(h) && t.forall(p)
  }

  def exists(p: T => Boolean) = !forall(!p(_))

  def find(p: T => Boolean): Option[T] = { this match {
    case Nil() => None[T]()
    case Cons(h, t) if p(h) => Some(h)
    case Cons(_, t) => t.find(p)
  }} ensuring { res => !res.isDefined || content.contains(res.get) }

  def groupBy[R](f: T => R): Map[R, List[T]] = this match {
    case Nil() => Map.empty[R, List[T]]
    case Cons(h, t) =>
      val key: R = f(h)
      val rest: Map[R, List[T]] = t.groupBy(f)
      val prev: List[T] = if (rest isDefinedAt key) rest(key) else Nil[T]()
      (rest ++ Map((key, h :: prev))) : Map[R, List[T]]
  }

  def takeWhile(p: T => Boolean): List[T] = { this match {
    case Cons(h,t) if p(h) => Cons(h, t.takeWhile(p))
    case _ => Nil[T]()
  }} ensuring { res =>
    (res forall p) &&
    (res.size <= this.size) &&
    (res.content subsetOf this.content)
  }

  def dropWhile(p: T => Boolean): List[T] = { this match {
    case Cons(h,t) if p(h) => t.dropWhile(p)
    case _ => this
  }} ensuring { res =>
    (res.size <= this.size) &&
    (res.content subsetOf this.content) &&
    (res.isEmpty || !p(res.head))
  }

  def count(p: T => Boolean): BigInt = { this match {
    case Nil() => BigInt(0)
    case Cons(h, t) =>
      (if (p(h)) BigInt(1) else BigInt(0)) + t.count(p)
  }} ensuring {
    _ == this.filter(p).size
  }

}

@ignore
object List {
  def apply[T](elems: T*): List[T] = {
    var l: List[T] = Nil[T]()
    for (e <- elems) {
      l = Cons(e, l)
    }
    l.reverse
  }
}

@library
object ListOps {
  def flatten[T](ls: List[List[T]]): List[T] = ls match {
    case Cons(h, t) => h ++ flatten(t)
    case Nil() => Nil()
  }

  def isSorted(ls: List[BigInt]): Boolean = ls match {
    case Nil() => true
    case Cons(_, Nil()) => true
    case Cons(h1, Cons(h2, _)) if(h1 > h2) => false
    case Cons(_, t) => isSorted(t)
  }

  def sorted(ls: List[BigInt]): List[BigInt] = { ls match {
    case Cons(h, t) => sortedIns(sorted(t), h)
    case Nil() => Nil()
  }} ensuring { isSorted _ }

  private def sortedIns(ls: List[BigInt], v: BigInt): List[BigInt] = {
    require(isSorted(ls))
    ls match {
      case Nil() => Cons(v, Nil())
      case Cons(h, t) =>
        if (v <= h) {
          Cons(v, t)
        } else {
          Cons(h, sortedIns(t, v))
        }
    }
  } ensuring { isSorted _ }
}

case class Cons[T](h: T, t: List[T]) extends List[T]
case class Nil[T]() extends List[T]

import ListOps._

@library
object ListSpecs {
  def snocIndex[T](l : List[T], t : T, i : BigInt) : Boolean = {
    require(0 <= i && i < l.size + 1)
    ((l :+ t).apply(i) == (if (i < l.size) l(i) else t)) because
    (l match {
      case Nil() => true
      case Cons(x, xs) => if (i > 0) snocIndex[T](xs, t, i-1) else true
    })
  }.holds

  def reverseIndex[T](l : List[T], i : BigInt) : Boolean = {
    require(0 <= i && i < l.size)
    (l match {
      case Nil() => true
      case Cons(x,xs) => snocIndex(l, x, i) && reverseIndex[T](l,i)
    }) &&
    (l.reverse.apply(i) == l.apply(l.size - 1 - i))
  }.holds

  def snocLast[T](l: List[T], x: T): Boolean = {
    ((l :+ x).last == x) because {
      l match {
        case Nil() => true
        case Cons(y, ys) => {
          ((y :: ys) :+ x).last   ==| trivial         |
          (y :: (ys :+ x)).last   ==| trivial         |
          (ys :+ x).last          ==| snocLast(ys, x) |
          x
        }.qed
      }
    }
  }.holds

  def headReverseLast[T](l: List[T]): Boolean = {
    require (!l.isEmpty)
    (l.head == l.reverse.last) because {
      l match {
        case Cons(x, xs) => {
          (x :: xs).head           ==| trivial                 |
          x                        ==| snocLast(xs.reverse, x) |
          (xs.reverse :+ x).last   ==| trivial                 |
          (x :: xs).reverse.last
        }.qed
      }
    }
  }.holds

  def appendIndex[T](l1 : List[T], l2 : List[T], i : BigInt) : Boolean = {
    require(0 <= i && i < l1.size + l2.size)
    ( (l1 ++ l2).apply(i) == (if (i < l1.size) l1(i) else l2(i - l1.size)) ) because {
      l1 match {
        case Nil() => true
        case Cons(x,xs) =>
          (i != BigInt(0)) ==> appendIndex[T](xs, l2, i - 1)
      }
    }
  }.holds

  @induct
  def appendAssoc[T](l1 : List[T], l2 : List[T], l3 : List[T]) : Boolean = {
    (l1 ++ l2) ++ l3 == l1 ++ (l2 ++ l3)
  }.holds

  def rightUnitAppend[T](l1 : List[T]) : Boolean = {
    (l1 ++ Nil() == l1) because {
      l1 match {
        case Nil() => true
        case Cons(x, xs) => rightUnitAppend(xs)
      }
    }
  }.holds

  def snocIsAppend[T](l : List[T], t : T) : Boolean = {
    ( (l :+ t) == l ++ Cons[T](t, Nil()) ) because {
      l match {
        case Nil() => true
        case Cons(x,xs) => snocIsAppend(xs,t)
      }
    }
  }.holds

  def snocAfterAppend[T](l1 : List[T], l2 : List[T], t : T) : Boolean = {
    ( (l1 ++ l2) :+ t == l1 ++ (l2 :+ t) ) because {
      l1 match {
        case Nil() => true
        case Cons(x,xs) => snocAfterAppend(xs,l2,t)
      }
    }
  }.holds

  def snocReverse[T](l : List[T], t : T) : Boolean = {
    ( (l :+ t).reverse == Cons(t, l.reverse) ) because {
      l match {
        case Nil() => true
        case Cons(x,xs) => snocReverse(xs,t)
      }
    }
  }.holds

  def reverseReverse[T](l : List[T]) : Boolean = {
    ( l.reverse.reverse == l ) because {
      l match {
        case Nil() =>
          true
        case Cons(x,xs) =>
          reverseReverse[T](xs) && snocReverse[T](xs.reverse, x)
      }
    }
  }.holds

  def reverseAppend[T](l1 : List[T], l2 : List[T]) : Boolean = {
    ( (l1 ++ l2).reverse == l2.reverse ++ l1.reverse ) because {
      l1 match {
        case Nil() => {
          (Nil() ++ l2).reverse         ==| trivial                     |
          l2.reverse                    ==| rightUnitAppend(l2.reverse) |
          l2.reverse ++ Nil()           ==| trivial                     |
          l2.reverse ++ Nil().reverse
        }.qed
        case Cons(x, xs) => {
          ((x :: xs) ++ l2).reverse         ==| trivial               |
          (x :: (xs ++ l2)).reverse         ==| trivial               |
          (xs ++ l2).reverse :+ x           ==| reverseAppend(xs, l2) |
          (l2.reverse ++ xs.reverse) :+ x   ==|
            snocAfterAppend(l2.reverse, xs.reverse, x)                |
          l2.reverse ++ (xs.reverse :+ x)   ==| trivial               |
          l2.reverse ++ (x :: xs).reverse
        }.qed
      }
    }
  }.holds

  def snocFoldRight[A, B](xs: List[A], y: A, z: B, f: (A, B) => B): Boolean = {
    ( (xs :+ y).foldRight(z)(f) == xs.foldRight(f(y, z))(f) ) because {
      xs match {
        case Nil() => true
        case Cons(x, xs) => snocFoldRight(xs, y, z, f)
      }
    }
  }.holds

  def folds[A, B](xs: List[A], z: B, f: (B, A) => B): Boolean = {
    val f2 = (x: A, z: B) => f(z, x)
    ( xs.foldLeft(z)(f) == xs.reverse.foldRight(z)(f2) ) because {
      xs match {
        case Nil() => true
        case Cons(x, xs) => {
          (x :: xs).foldLeft(z)(f)              ==| trivial               |
          xs.foldLeft(f(z, x))(f)               ==| folds(xs, f(z, x), f) |
          xs.reverse.foldRight(f(z, x))(f2)     ==| trivial               |
          xs.reverse.foldRight(f2(x, z))(f2)    ==|
            snocFoldRight(xs.reverse, x, z, f2)                           |
          (xs.reverse :+ x).foldRight(z)(f2)    ==| trivial               |
          (x :: xs).reverse.foldRight(z)(f2)
        }.qed
      }
    }
  }.holds

  def scanVsFoldLeft[A, B](l : List[A], z: B, f: (B, A) => B): Boolean = {
    ( l.scanLeft(z)(f).last == l.foldLeft(z)(f) ) because {
      l match {
        case Nil() => true
        case Cons(x, xs) => scanVsFoldLeft(xs, f(z, x), f)
      }
    }
  }.holds

  @induct
  def scanVsFoldRight[A,B](l: List[A], z: B, f: (A,B) => B): Boolean = {
    l.scanRight(z)(f).head == l.foldRight(z)(f)
  }.holds

  def appendContent[A](l1: List[A], l2: List[A]) = {
    l1.content ++ l2.content == (l1 ++ l2).content
  }.holds

  def flattenPreservesContent[T](ls: List[List[T]]): Boolean = {
    val f: (List[T], Set[T]) => Set[T] = _.content ++ _
    ( flatten(ls).content == ls.foldRight(Set[T]())(f) ) because {
      ls match {
        case Nil() => true
        case Cons(h, t) => {
          flatten(h :: t).content                     ==| trivial                       |
          (h ++ flatten(t)).content                   ==| appendContent(h, flatten(t))  |
          h.content ++ flatten(t).content             ==| flattenPreservesContent(t)    |
          h.content ++ t.foldRight(Set[T]())(f)       ==| trivial                       |
          f(h, Set[T]()) ++ t.foldRight(Set[T]())(f)  ==| trivial                       |
          (h :: t).foldRight(Set[T]())(f)
        }.qed
      }
    }
  }.holds

}
