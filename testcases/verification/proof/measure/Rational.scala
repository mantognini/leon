/* Copyright 2009-2015 EPFL, Lausanne */

package leon.testcases.verification.proof.measure

import leon.lang._
import scala.language.implicitConversions

object Rational {
  implicit def bigInt2Rational(x: BigInt) = Rational(x, 1)
}

// Represents rational number n/d, where n is the numerator and d the denumerator
case class Rational (n: BigInt, d: BigInt) {

  def +(that: Rational): Rational = {
    require(isRational && that.isRational)
    Rational(n * that.d + that.n * d, d * that.d)
  } ensuring { _.isRational }

  def -(that: Rational): Rational = {
    require(isRational && that.isRational)
    Rational(n * that.d - that.n * d, d * that.d)
  } ensuring { _.isRational }

  def *(that: Rational): Rational = {
    require(isRational && that.isRational)
    Rational(n * that.n, d * that.d)
  } ensuring { _.isRational }

  def /(that: Rational): Rational = {
    require(isRational && that.isRational && that.nonZero)
    Rational(n * that.d, d * that.n)
  } ensuring { _.isRational }

  def <=(that: Rational): Boolean = {
    require(isRational && that.isRational)
    n * that.d <= d * that.n
  }

  def >=(that: Rational): Boolean = {
    require(isRational && that.isRational)
    that <= this
  }

  // Equivalence of two rationals, true if they represent the same real number
  def ~(that: Rational): Boolean = {
    require(isRational && that.isRational)
    n * that.d == that.n * d
  }

  def isRational = d != 0
  def nonZero = n != 0

}

object RationalSpecs {

  def equivalenceOverAddition(a1: Rational, a2: Rational, b1: Rational, b2: Rational): Boolean = {
    require(
      a1.isRational && a2.isRational && b1.isRational && b2.isRational &&
        a1 ~ a2 && b1 ~ b2
    )

    (a1 + b1) ~ (a2 + b2)
  }.holds

  def equivalenceOverSubstraction(a1: Rational, a2: Rational, b1: Rational, b2: Rational): Boolean = {
    require(
      a1.isRational && a2.isRational && b1.isRational && b2.isRational &&
        a1 ~ a2 && b1 ~ b2
    )

    (a1 - b1) ~ (a2 - b2)
  }.holds

  def equivalenceOverMultiplication(a1: Rational, a2: Rational, b1: Rational, b2: Rational): Boolean = {
    require(
      a1.isRational && a2.isRational && b1.isRational && b2.isRational &&
        a1 ~ a2 && b1 ~ b2
    )

    (a1 * b1) ~ (a2 * b2)
  }.holds

  def equivalenceOverDivision(a1: Rational, a2: Rational, b1: Rational, b2: Rational): Boolean = {
    require(
      a1.isRational && a2.isRational && b1.isRational && b2.isRational &&
        a1 ~ a2 && b1 ~ b2 &&
        b1.nonZero // in addition to the usual requirements
    )

    (a1 / b1) ~ (a2 / b2)
  }.holds

  def orderingPreservedOverAddition(a: Rational, b: Rational, c: Rational): Boolean = {
    require(a.isRational && b.isRational && c.isRational)

    (a <= b) ==> ((a + c) <= (b + c))
  }.holds

}

