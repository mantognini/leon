/* Copyright 2009-2014 EPFL, Lausanne */
package leon

import leon.annotation._
import leon.lang._
import scala.language.implicitConversions

import leon.proof.Internal._

package object proof {

  case class ProofOps(prop: Boolean) {
    def because(proof: Boolean): Boolean = proof && prop
    def neverHolds: Boolean = {
      require(!prop)
      !prop
    }
  }

  implicit def boolean2ProofOps(prop: Boolean): ProofOps = ProofOps(prop)

  def trivial: Boolean = true

  def by(proof: Boolean)(prop: Boolean): Boolean =
    proof && prop

  /**
   * Relational reasoning.
   *
   *         {
   *           ((y :: ys) :+ x).last   ^^ _ == _ ^^| trivial         |
   *           (y :: (ys :+ x)).last   ==| trivial         |
   *           (ys :+ x).last          ==| snocLast(ys, x) |
   *           x
   *         }.qed
   */
  case class RelReasoning[A](x: A, prop: Boolean) {

    def ^^[B](r: (A, B) => Boolean): WithRel[A, B] = WithRel(x, r, prop)

    /** Short-hand for equational reasoning. */
    def ==|(proof: Boolean): WithProof[A, A] = {
      require(proof)
      WithProof(x, _ == _, proof, prop)
    }

    def qed: Boolean = prop
  }

  implicit def any2RelReasoning[A](x: A): RelReasoning[A] =
    RelReasoning(x, true)

  /*
  case class EqReasoning[A](x: A, prop: Boolean) {
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
   */
}
