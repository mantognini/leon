/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import purescala.Expressions._
import leon.utils.ASCIIHelpers._

sealed abstract class Example {
  def ins: Seq[Expr]

  def asString(implicit ctx: LeonContext) = {
    def esToStr(es: Seq[Expr]): String = {
      es.map(_.asString).mkString("(", ", ", ")")
    }

    this match {
      case InExample(ins)          => esToStr(ins)
      case InOutExample(ins, outs) => esToStr(ins)+" ~> "+esToStr(outs)
    }
  }
}

case class InOutExample(ins: Seq[Expr], outs: Seq[Expr]) extends Example
case class InExample(ins: Seq[Expr]) extends Example
