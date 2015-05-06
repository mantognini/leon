/* Copyright 2009-2015 EPFL, Lausanne */

package leon.collection

import leon._
import leon.lang._
import leon.annotation._
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
  }) ensuring { res => res == (content contains v) }

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
    case (Nil(), _) => Nil()
    case (Cons(h, t), i) =>
      if (i <= BigInt(0)) {
        Nil()
      } else {
        Cons(h, t.take(i-1))
      }
  }} ensuring { _.size == (
    if      (i <= 0)         BigInt(0)
    else if (i >= this.size) this.size
    else                     i
  )}

  def drop(i: BigInt): List[T] = { (this, i) match {
    case (Nil(), _) => Nil()
    case (Cons(h, t), i) =>
      if (i <= BigInt(0)) {
        Cons(h, t)
      } else {
        t.drop(i-1)
      }
  }} ensuring { _.size == (
    if      (i <= 0)         this.size
    else if (i >= this.size) BigInt(0)
    else                     this.size - i
  )}

  def slice(from: BigInt, to: BigInt): List[T] = {
    require(0 <= from && from <= to && to <= size)
    drop(from).take(to-from)
  }

  def replace(from: T, to: T): List[T] = { this match {
    case Nil() => Nil()
    case Cons(h, t) =>
      val r = t.replace(from, to)
      if (h == from) {
        Cons(to, r)
      } else {
        Cons(h, r)
      }
  }} ensuring { res =>
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
    case (_) =>
      Nil()
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
      Nil()
  }} ensuring { _.content == this.content -- Set(e) }

  def --(that: List[T]): List[T] = { this match {
    case Cons(h, t) =>
      if (that.contains(h)) {
        t -- that
      } else {
        Cons(h, t -- that)
      }
    case Nil() =>
      Nil()
  }} ensuring { _.content == this.content -- that.content }

  def &(that: List[T]): List[T] = { this match {
    case Cons(h, t) =>
      if (that.contains(h)) {
        Cons(h, t & that)
      } else {
        t & that
      }
    case Nil() =>
      Nil()
  }} ensuring { _.content == (this.content & that.content) }

  def pad(s: BigInt, e: T): List[T] = (this, s) match {
    case (_, s) if s <= 0 =>
      this
    case (Nil(), s) =>
      Cons(e, Nil().pad(s-1, e))
    case (Cons(h, t), s) =>
      Cons(h, t.pad(s-1, e))
  }

  def find(e: T): Option[BigInt] = { this match {
    case Nil() => None()
    case Cons(h, t) =>
      if (h == e) {
        Some(0)
      } else {
        t.find(e) match {
          case None()  => None()
          case Some(i) => Some(i+1)
        }
      }
  }} ensuring { _.isDefined == this.contains(e) }

  def init: List[T] = (this match {
    case Cons(h, Nil()) =>
      Nil[T]()
    case Cons(h, t) =>
      Cons[T](h, t.init)
    case Nil() =>
      Nil[T]()
  }) ensuring ( (r: List[T]) => ((r.size < this.size) || (this.size == BigInt(0))) )

  def last: T = {
    require(!isEmpty)
    this match {
      case Cons(h, Nil()) => h
      case Cons(_, t) => t.last
    }
  }

  def lastOption: Option[T] = this match {
    case Cons(h, t) =>
      t.lastOption.orElse(Some(h))
    case Nil() =>
      None()
  }

  def firstOption: Option[T] = this match {
    case Cons(h, t) =>
      Some(h)
    case Nil() =>
      None()
  }

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

  def count(e: T): BigInt = this match {
    case Cons(h, t) =>
      if (h == e) {
        1 + t.count(e)
      } else {
        t.count(e)
      }
    case Nil() =>
      BigInt(0)
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
  }

  def rotate(s: BigInt): List[T] = {
    if (s < 0) {
      rotate(size+s)
    } else {
      val s2 = s % size
      drop(s2) ++ take(s2)
    }
  }

  def isEmpty = this match {
    case Nil() => true
    case _ => false
  }

  // Higher-order API
  def map[R](f: T => R): List[R] = { this match {
    case Nil() => Nil()
    case Cons(h, t) => f(h) :: t.map(f)
  }} ensuring { _.size == this.size}

  def foldLeft[R](z: R)(f: (R,T) => R): R = this match {
    case Nil() => z
    case Cons(h,t) => t.foldLeft(f(z,h))(f)
  }

  def foldRight[R](f: (T,R) => R)(z: R): R = this match {
    case Nil() => z
    case Cons(h, t) => f(h, t.foldRight(f)(z))
  }

  def scanLeft[R](z: R)(f: (R,T) => R): List[R] = this match {
    case Nil() => z :: Nil()
    case Cons(h,t) => z :: t.scanLeft(f(z,h))(f)
  }

  def scanRight[R](f: (T,R) => R)(z: R): List[R] = { this match {
    case Nil() => z :: Nil()
    case Cons(h, t) =>
      val rest@Cons(h1,_) = t.scanRight(f)(z)
      f(h, h1) :: rest
  }} ensuring { !_.isEmpty }

  def flatMap[R](f: T => List[R]): List[R] =
    ListOps.flatten(this map f)

  def filter(p: T => Boolean): List[T] = { this match {
    case Nil() => Nil()
    case Cons(h, t) if p(h) => Cons(h, t.filter(p))
    case Cons(_, t) => t.filter(p)
  }} ensuring { res => res.size <= this.size && res.forall(p) }

  // In case we implement for-comprehensions
  def withFilter(p: T => Boolean) = filter(p)

  def forall(p: T => Boolean): Boolean = this match {
    case Nil() => true
    case Cons(h, t) => p(h) && t.forall(p)
  }

  def exists(p: T => Boolean) = !forall(!p(_))

  def find(p: T => Boolean): Option[T] = { this match {
    case Nil() => None()
    case Cons(h, t) if p(h) => Some(h)
    case Cons(_, t) => t.find(p)
  }} ensuring { _.isDefined == exists(p) }

  // FIXME: I keep getting these weird type errors
  //def groupBy[R](f: T => R): Map[R, List[T]] = this match {
  //  case Nil() => Map.empty[R, List[T]]
  //  case Cons(h, t) =>
  //    val key: R = f(h)
  //    val rest: Map[R, List[T]] = t.groupBy(f)
  //    val prev: List[T] = if (rest isDefinedAt key) rest(key) else Nil[T]()
  //    (rest ++ Map((key, h :: prev))) : Map[R, List[T]]
  //}

  def takeWhile(p: T => Boolean): List[T] = { this match {
    case Cons(h,t) if p(h) => Cons(h, t.takeWhile(p))
    case _ => Nil[T]()
  }} ensuring { _ forall p }
}

@ignore
object List {
  def apply[T](elems: T*): List[T] = ???
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

  def sorted(ls: List[BigInt]): List[BigInt] = ls match {
    case Cons(h, t) => insSort(sorted(t), h)
    case Nil() => Nil()
  }

  def insSort(ls: List[BigInt], v: BigInt): List[BigInt] = ls match {
    case Nil() => Cons(v, Nil())
    case Cons(h, t) =>
      if (v <= h) {
        Cons(v, t)
      } else {
        Cons(h, insSort(t, v))
      }
  }
}

case class Cons[T](h: T, t: List[T]) extends List[T]
case class Nil[T]() extends List[T]

@library
object ListSpecs {
  def snocIndex[T](l : List[T], t : T, i : BigInt) : Boolean = {
    require(0 <= i && i < l.size + 1)
    // proof:
    (l match {
      case Nil() => true
      case Cons(x, xs) => if (i > 0) snocIndex[T](xs, t, i-1) else true
    }) &&
    // claim:
    ((l :+ t).apply(i) == (if (i < l.size) l(i) else t))
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
    (l :+ x).last == x because {
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
    l.head == l.reverse.last because {
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
    (l1 match {
      case Nil() => true
      case Cons(x,xs) => if (i==BigInt(0)) true else appendIndex[T](xs,l2,i-1)
    }) &&
    ((l1 ++ l2).apply(i) == (if (i < l1.size) l1(i) else l2(i - l1.size)))
  }.holds

  def appendAssoc[T](l1 : List[T], l2 : List[T], l3 : List[T]) : Boolean = {
    (l1 match {
      case Nil() => true
      case Cons(x,xs) => appendAssoc(xs,l2,l3)
    }) &&
    (((l1 ++ l2) ++ l3) == (l1 ++ (l2 ++ l3)))
  }.holds

  def rightIdAppend[T](l1 : List[T]) : Boolean = {
    (l1 match {
      case Nil() => true
      case Cons(x, xs) => rightIdAppend(xs)
    }) &&
    ((l1 ++ Nil()) == l1)
  }.holds

  def snocIsAppend[T](l : List[T], t : T) : Boolean = {
    (l match {
      case Nil() => true
      case Cons(x,xs) =>  snocIsAppend(xs,t)
    }) &&
    ((l :+ t) == l ++ Cons[T](t, Nil()))
  }.holds

  def snocAfterAppend[T](l1 : List[T], l2 : List[T], t : T) : Boolean = {
    (l1 match {
      case Nil() => true
      case Cons(x,xs) =>  snocAfterAppend(xs,l2,t)
    }) &&
    ((l1 ++ l2) :+ t == (l1 ++ (l2 :+ t)))
  }.holds

  def snocReverse[T](l : List[T], t : T) : Boolean = {
    (l match {
      case Nil() => true
      case Cons(x,xs) => snocReverse(xs,t)
    }) &&
    ((l :+ t).reverse == Cons(t, l.reverse))
  }.holds

  def reverseReverse[T](l : List[T]) : Boolean = {
    (l match {
      case Nil() => true
      case Cons(x,xs) => reverseReverse[T](xs) && snocReverse[T](xs.reverse, x)
    }) &&
    (l.reverse.reverse == l)
  }.holds

  def reverseAppend[T](l1 : List[T], l2 : List[T]) : Boolean = {
    (l1 ++ l2).reverse == (l2.reverse ++ l1.reverse) because {
      l1 match {
        case Nil() => {
          (Nil() ++ l2).reverse         ==| trivial                   |
          l2.reverse                    ==| rightIdAppend(l2.reverse) |
          l2.reverse ++ Nil()           ==| trivial                   |
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
    (xs :+ y).foldRight(f)(z) == xs.foldRight(f)(f(y, z)) because {
      xs match {
        case Nil() => true
        case Cons(x, xs) => snocFoldRight(xs, y, z, f)
      }
    }
  }.holds

  def folds[A, B](xs: List[A], z: B, f: (B, A) => B): Boolean = {
    val f2 = (x: A, z: B) => f(z, x)
    xs.foldLeft(z)(f) == xs.reverse.foldRight(f2)(z) because {
      xs match {
        case Nil() => true
        case Cons(x, xs) => {
          (x :: xs).foldLeft(z)(f)              ==| trivial               |
          xs.foldLeft(f(z, x))(f)               ==| folds(xs, f(z, x), f) |
          xs.reverse.foldRight(f2)(f(z, x))     ==| trivial               |
          xs.reverse.foldRight(f2)(f2(x, z))    ==|
            snocFoldRight(xs.reverse, x, z, f2)                           |
          (xs.reverse :+ x).foldRight(f2)(z)    ==| trivial               |
          (x :: xs).reverse.foldRight(f2)(z)
        }.qed
      }
    }
  }.holds

  /* This doesn't verify. */
  def folds3[A, B](
    xs: List[A], z: B, fl: (B, A) => B, fr: (A, B) => B): Boolean = {

    /* Additional hyp. */
    require {
      forall((x: A, z: B) => fl(z, x) == fr(x, z))
    }

    xs.foldLeft(z)(fl) == xs.reverse.foldRight(fr)(z) because {
      xs match {
        case Nil() => true
        case Cons(x, xs) => {
          (x :: xs).foldLeft(z)(fl)    ==| trivial                      |
          xs.foldLeft(fl(z, x))(fl)    ==| folds3(xs, fl(z, x), fl, fr) |
          xs.reverse.foldRight(fr)(fl(z, x))   ==| trivial /* hyp. */   |
          xs.reverse.foldRight(fr)(fr(x, z))   ==|
            snocFoldRight(xs, x, z, fr)                                 |
          (xs.reverse :+ x).foldRight(fr)(z)   ==| trivial              |
          (x :: xs).reverse.foldRight(fr)(z)
        }.qed
      }
    }
  }.holds

  /* A minimized version of fold3 that still doesn't verify. */
  def foo2[A, B](
    xs: List[A], x: A, z: B, fl: (B, A) => B, fr: (A, B) => B): Boolean = {

    /* Additional hyp. */
    require {
      forall((x: A, z: B) => fl(z, x) == fr(x, z))
    }

    (xs.foldRight(fr)(fr(x, z)) == (xs :+ x).foldRight(fr)(z)) &&
    snocFoldRight(xs, x, z, fr)
  }.holds

  def scanVsFoldLeft[A, B](l : List[A], z: B, f: (B, A) => B): Boolean = {
    l.scanLeft(z)(f).last == l.foldLeft(z)(f) because {
      l match {
        case Nil() => true
        case Cons(x, xs) => scanVsFoldLeft(xs, f(z, x), f)
      }
    }
  }.holds

  @induct
  def scanVsFoldRight[A,B](l: List[A], z: B, f: (A,B) => B): Boolean = {
    l.scanRight(f)(z).head == l.foldRight(f)(z)
  }.holds

}
