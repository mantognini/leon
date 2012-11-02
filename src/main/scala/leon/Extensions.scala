package leon

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Definitions._

object Extensions {
  import leon.verification.{Analyser,Tactic}
  import leon.solvers.Solver

  abstract class Extension(reporter: Reporter) {
    def description: String
    def shortDescription: String = description
  }

  // The rest of the code is for dynamically loading extensions

  private var allLoaded : Seq[Extension] = Nil
  private var analysisExtensions : Seq[Analyser] = Nil
  private var solverExtensions : Seq[Solver] = Nil

  // Returns the list of the newly loaded.
  def loadAll(extensionsReporter : Reporter = Settings.reporter) : Seq[Extension] = {
    val allNames: Seq[String] = Settings.extensionNames
    val loaded = (if(!allNames.isEmpty) {
      val classLoader = Extensions.getClass.getClassLoader

      val classes: Seq[Class[_]] = (for(name <- allNames) yield {
        try {
          classLoader.loadClass(name)
        } catch {
          case _ => {
            Settings.reporter.error("Couldn't load extension class " + name) 
            null
          }
        }
      }).filter(_ != null)

      classes.map(cl => {
        try {
          val cons = cl.getConstructor(classOf[Reporter])
          cons.newInstance(extensionsReporter).asInstanceOf[Extension]
        } catch {
          case _ => {
            Settings.reporter.error("Extension class " + cl.getName + " does not seem to be of a proper type.")
            null
          }
        }
      }).filter(_ != null)
    } else {
      Nil
    })
    if(!loaded.isEmpty) {
      Settings.reporter.info("The following extensions are loaded:\n" + loaded.toList.map(_.description).mkString("  ", "\n  ", ""))
    }
    // these extensions are always loaded, unless specified otherwise
    val defaultExtensions: Seq[Extension] = if(Settings.runDefaultExtensions) {
      val z3 : Solver = new solvers.z3.FairZ3Solver(extensionsReporter)
      z3 :: Nil
    } else {
      Nil
    }

    allLoaded = defaultExtensions ++ loaded
    analysisExtensions = allLoaded.filter(_.isInstanceOf[Analyser]).map(_.asInstanceOf[Analyser])
    //analysisExtensions = new TestGeneration(extensionsReporter) +: analysisExtensions

    val solverExtensions0 = allLoaded.filter(_.isInstanceOf[Solver]).map(_.asInstanceOf[Solver])
    val solverExtensions1 = if(Settings.useQuickCheck) new solvers.RandomSolver(extensionsReporter) +: solverExtensions0 else solverExtensions0
    val solverExtensions2 = if(Settings.useParallel) Seq(new solvers.ParallelSolver(solverExtensions1: _*)) else solverExtensions1
    val solverExtensions3 = 
      if(Settings.solverTimeout == None) {
        solverExtensions2 
      } else {
        val t = Settings.solverTimeout.get 
        solverExtensions2.map(s => new solvers.TimeoutSolver(s, t))
      }
    solverExtensions = solverExtensions3
    loaded
  }

  def loadedExtensions : Seq[Extension] = allLoaded
  def loadedAnalysisExtensions : Seq[Analyser] = analysisExtensions
  def loadedSolverExtensions : Seq[Solver] = solverExtensions
}