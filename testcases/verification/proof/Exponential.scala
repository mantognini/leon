/* Copyright 2009-2015 EPFL, Lausanne */

package leon.testcases.verification.math

import leon.annotation._
import leon.lang._
import leon.proof._

object Exponential {

  /** A simple, but slow function for computing exponentials. */
  def exp(x: BigInt, y: BigInt): BigInt = {
    require(y >= 0)
    if      (x == 0) 0
    else if (y == 0) 1
    else             x * exp(x, y - 1)
  }

  /** The exponential function is monotone. */
  def monotone(x: BigInt, y: BigInt): Boolean = {
    require(y >= 0 && x > 0)
    exp(x, y) > 0 because {
      if (y == 0) trivial
      else        check {
        x > 0 && exp(x, y - 1) > 0 because monotone(x, y - 1)
      }
    }
  }.holds

  /** The exponential function is monotone (short proof). */
  def monotoneShort(x: BigInt, y: BigInt): Boolean = {
    require(y >= 0 && x > 0)
    exp(x, y) > 0 because {
      if (y == 0) trivial
      else        monotoneShort(x, y - 1)
    }
  }.holds


  /**
   * The exponential function (with respect to a fixed base) is a
   * homomorphism between the commutative monoids of addition and
   * multiplication over integers.
   */
  def monoidHom(x: BigInt, y: BigInt, z: BigInt): Boolean = {
    require(y >= 0 && z >= 0)
    exp(x, y + z) == exp(x, y) * exp(x, z) because {
      if      (x == 0) trivial
      else if (y == 0) trivial
      else             {
        exp(x, y + z)                 ==| (y + z != 0)           |
        x * exp(x, y + z - 1)         ==| monoidHom(x, y - 1, z) |
        x * exp(x, y - 1) * exp(x, z)
      }.qed
    }
  }.holds

  /**
   * Exponentiation (by a fixed exponent) commutes with
   * multiplication.
   */
  def expMultCommute(x: BigInt, y: BigInt, z: BigInt): Boolean = {
    require(z >= 0)
    exp(x * y, z) == exp(x, z) * exp(y, z) because {
      if      (x == 0) trivial
      else if (y == 0) trivial
      else if (z == 0) trivial
      else             check {
        x * y * exp(x * y, z - 1) ==
          x * exp(x, z - 1) * y * exp(y, z - 1) because
          expMultCommute(x, y, z - 1)
      }
    }
  }.holds

  /** A combination of the previous two lemmas. */
  def square(x: BigInt, y: BigInt): Boolean = {
    require(y >= 0)
    exp(x, 2 * y) == exp(x * x, y) because
      monoidHom(x, y, y) && expMultCommute(x, x, y)
  }.holds

  /** A more efficient function for computing exponentials. */
  def fastExp(x: BigInt, y: BigInt): BigInt = {
    require(y >= 0)
    if      (x == 0)     0
    else if (y == 0)     1
    else if (y % 2 == 0) fastExp(x * x, y / 2)
    else                 x * fastExp(x, y - 1)
  } ensuring { res =>
    res == exp(x, y) because {
      if      (x == 0)     trivial
      else if (y == 0)     trivial
      else if (y % 2 == 0) {
        val z = y / 2; {
          res                   ==| trivial                 |
          fastExp(x * x, z)     ==| trivial /* ind. hyp. */ |
          exp(x * x, z)         ==| square(x, z)            |
          exp(x, y)
        }.qed
      }
      else                 {
        val z = (y - 1) / 2; {
          res                   ==| (y % 2 != 0)            |
          x * fastExp(x * x, z) ==| {
            fastExp(x * x, z)   ==| trivial /* ind. hyp. */ |
            exp(x * x, z)       ==| square(x, z)            |
            exp(x, 2 * z)       ==| trivial                 |
            exp(x, y - 1)                             }.qed |
          x * exp(x, y - 1)     ==| (y != 0)                |
          exp(x, y)
        }.qed
      }
    }
  }
}

