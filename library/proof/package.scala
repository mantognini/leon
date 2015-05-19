/* Copyright 2009-2014 EPFL, Lausanne */
package leon

import leon.annotation._
import scala.language.implicitConversions

package object proof {

  case class ProofOps(prop: Boolean) {
    def because(proof: Boolean): Boolean = proof && prop
    def implies(that: Boolean): Boolean = !prop || that
    def fallacy: Boolean = { // TODO this is probaly not the right verb...
      require(!prop)
      prop
    }
  }

  implicit def boolean2ProofOps(prop: Boolean): ProofOps = ProofOps(prop)

  def trivial: Boolean = true
  def trivially(x: Boolean) = x // identity

  def by(proof: Boolean)(prop: Boolean): Boolean =
    proof && prop

  case class EqReasoning[A](x: A, prop: Boolean) {
    def ==|(proof: Boolean): EqReasoning[A] = {
      require(proof)
      EqReasoning(x, prop)
    }

    def |(that: EqReasoning[A]): EqReasoning[A] = {
      require(this.x == that.x)
      EqReasoning(that.x, this.prop && that.prop)
    }

    def qed: Boolean = prop
  }

  implicit def any2EqReasoning[A](x: A): EqReasoning[A] = EqReasoning(x, true)

  case class ImplicationReasoning[A](x: A, prop: Boolean) {
    def ==>|(f: A => Boolean): ImplicationReasoning[A] = {
      require(prop implies f(x))
      ImplicationReasoning(x, f(x))
      // ImplicationReasoning(x, prop implies f(x))    <- this is wrong because
      //                                                  we propagate false all
      //                                                  the way to the end
    }

    def |[B](that: ImplicationReasoning[B]): ImplicationReasoning[B] = {
      ImplicationReasoning(that.x, this.prop implies that.prop)
    }

    def qed: Boolean = prop
  }

  implicit def any2ImplicationReasoning[A](x: A): ImplicationReasoning[A] = ImplicationReasoning(x, false)
}

