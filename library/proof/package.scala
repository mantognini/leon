/* Copyright 2009-2014 EPFL, Lausanne */
package leon

import leon.annotation._
import leon.lang._
import scala.language.implicitConversions

package object proof {

  case class ProofOps(prop: Boolean) {
    def because(proof: Boolean): Boolean = proof && prop
    def neverHolds: Boolean = {
      require(!prop)
      prop
    }
  }

  implicit def boolean2ProofOps(prop: Boolean): ProofOps = ProofOps(prop)

  def trivial: Boolean = true
  def trivially(x: Boolean) = x // identity

  def by(proof: Boolean)(prop: Boolean): Boolean =
    proof && prop

  case class EqReasoning[A](lhs: A, rhs: A, prop: Boolean) {
    // Invariant: lhs == rhs has been already checked
    def ==|(proof: Boolean): EqReasoning[A] = {
      require(proof)
      EqReasoning(lhs, rhs, proof)
    }

    def |(that: EqReasoning[A]): EqReasoning[A] = {
      require(this.prop ==> (this.rhs == that.lhs))
      EqReasoning(this.lhs, that.rhs, that.prop)
    }

    def qed: Boolean = lhs == rhs
  }

  implicit def any2EqReasoning[A](x: A): EqReasoning[A] = EqReasoning(x, x, true)

  case class ImplicationReasoning[A](x: A, prop: Boolean) {
    def ==>|(f: A => Boolean): ImplicationReasoning[A] = {
      require(prop ==> f(x))
      ImplicationReasoning(x, f(x))
      // ImplicationReasoning(x, prop ==> f(x))        <- this is wrong because
      //                                                  we propagate false all
      //                                                  the way to the end
    }

    def |[B](that: ImplicationReasoning[B]): ImplicationReasoning[B] = {
      ImplicationReasoning(that.x, this.prop ==> that.prop)
    }

    def qed: Boolean = prop
  }

  implicit def any2ImplicationReasoning[A](x: A): ImplicationReasoning[A] = ImplicationReasoning(x, false)
}

