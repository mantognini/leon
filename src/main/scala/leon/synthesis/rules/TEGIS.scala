/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.Types._
import grammars._
import utils._

case object TEGIS extends TEGISLike[TypeTree]("TEGIS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    TegisParams(
      grammar = Grammars.default(sctx, p),
      rootLabel = {(tpe: TypeTree) => tpe }
    )
  }
}
