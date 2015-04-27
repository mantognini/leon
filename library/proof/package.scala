/* Copyright 2009-2014 EPFL, Lausanne */
package leon

import leon.annotation._
import scala.language.implicitConversions

package object proof {

  case class ProofOps(prop: Boolean) {
    def because(proof: Boolean): Boolean = proof && prop
    def implies(that: Boolean): Boolean = !prop || that
  }

  implicit def boolean2ProofOps(prop: Boolean): ProofOps = ProofOps(prop)

  def trivial: Boolean = true

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
}
