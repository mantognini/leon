/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis
package rules

import purescala.ExprOps._
import purescala.Types._
import purescala.Extractors._
import utils._
import grammars._
import Witnesses._

case object CEGLESS extends CEGISLike[NonTerminal[String]]("CEGLESS") {
  def getParams(sctx: SynthesisContext, p: Problem) = {
    val TopLevelAnds(clauses) = p.ws

    val ctx = sctx.context

    val guides = clauses.collect {
      case Guide(e) => e
    }

    val inputs = p.as.map(_.toVariable)

    sctx.reporter.ifDebug { printer =>
    printer("Guides available:")
      for (g <- guides) {
        printer(" - "+g.asString(ctx))
      }
    }

    val guidedGrammar = Union(guides.map(SimilarTo(_, inputs.toSet, sctx, p)))

    CegisParams(
      grammar = guidedGrammar,
      rootLabel = { (tpe: TypeTree) => NonTerminal(tpe, "G0") },
      maxUnfoldings = (0 +: guides.map(depth(_) + 1)).max
    )
  }
}



