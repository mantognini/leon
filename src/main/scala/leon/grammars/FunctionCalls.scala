/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package grammars

import purescala.Types._
import purescala.TypeOps._
import purescala.Definitions._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Expressions._

case class FunctionCalls(prog: Program, currentFunction: FunDef, types: Seq[TypeTree], exclude: Set[FunDef]) extends ExpressionGrammar[TypeTree] {
   def computeProductions(t: TypeTree)(implicit ctx: LeonContext): Seq[Gen] = {

     def getCandidates(fd: FunDef): Seq[TypedFunDef] = {
       // Prevents recursive calls
       val cfd = currentFunction

       val isRecursiveCall = (prog.callGraph.transitiveCallers(cfd) + cfd) contains fd

       val isDet = fd.body.exists(isDeterministic)

       if (!isRecursiveCall && isDet) {
         val free = fd.tparams.map(_.tp)

         canBeSubtypeOf(fd.returnType, free, t, rhsFixed = true) match {
           case Some(tpsMap) =>
             val tfd = fd.typed(free.map(tp => tpsMap.getOrElse(tp, tp)))

             if (tpsMap.size < free.size) {
               /* Some type params remain free, we want to assign them:
                *
                * List[T] => Int, for instance, will be found when
                * requesting Int, but we need to assign T to viable
                * types. For that we use list of input types as heuristic,
                * and look for instantiations of T such that input <?:
                * List[T].
                */
               types.distinct.flatMap { (atpe: TypeTree) =>
                 var finalFree = free.toSet -- tpsMap.keySet
                 var finalMap = tpsMap

                 for (ptpe <- tfd.params.map(_.getType).distinct) {
                   canBeSubtypeOf(atpe, finalFree.toSeq, ptpe) match {
                     case Some(ntpsMap) =>
                       finalFree --= ntpsMap.keySet
                       finalMap  ++= ntpsMap
                     case _ =>
                   }
                 }

                 if (finalFree.isEmpty) {
                   List(fd.typed(free.map(tp => finalMap.getOrElse(tp, tp))))
                 } else {
                   Nil
                 }
               }
             } else {
               /* All type parameters that used to be free are assigned
                */
               List(tfd)
             }
           case None =>
             Nil
         }
       } else {
         Nil
       }
     }

     val filter = (tfd:TypedFunDef) => tfd.fd.isSynthetic || (exclude contains tfd.fd)
     val funcs = visibleFunDefsFromMain(prog).toSeq.sortBy(_.id).flatMap(getCandidates).filterNot(filter)

     funcs.map{ tfd =>
       nonTerminal(tfd.params.map(_.getType), { sub => FunctionInvocation(tfd, sub) })
     }
   }
  }
