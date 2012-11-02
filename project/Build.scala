import sbt._
import Process._
import Keys._

object Leon extends Build {
  private val scriptName = "leon"
  def scriptFile = file(".") / scriptName
  def is64 = System.getProperty("sun.arch.data.model") == "64"
  def ldLibraryDir32 = file(".") / "lib-bin" / "32"
  def ldLibraryDir64 = file(".") / "lib-bin" / "64"

  val cleanTask = TaskKey[Unit]("clean", "Cleans up the generated binaries and scripts.") <<= (streams, clean) map { (s,c) =>
    c
    if(scriptFile.exists && scriptFile.isFile) {
      scriptFile.delete
    }
  }

  val scriptTask = TaskKey[Unit]("script", "Generate the " + scriptName + " Bash script") <<= (streams, dependencyClasspath in Compile, classDirectory in Compile) map { (s, deps, out) =>
    if(scriptFile.exists) {
      s.log.info("Re-generating script ("+(if(is64) "64b" else "32b")+")...")
      scriptFile.delete
    } else {
      s.log.info("Generating script ("+(if(is64) "64b" else "32b")+")...")
    }
    try {
      val depsPaths = deps.map(_.data.absolutePath)

      // One ugly hack... Likely to fail for Windows, but it's a Bash script anyway.
      val scalaHomeDir = depsPaths.find(_.endsWith("lib/scala-library.jar")) match {
        case None => throw new Exception("Couldn't guess SCALA_HOME.")
        case Some(p) => p.substring(0, p.length - 21)
      }
      s.log.info("Will use " + scalaHomeDir + " as SCALA_HOME.")

      val nl = System.getProperty("line.separator")
      val fw = new java.io.FileWriter(scriptFile)
      fw.write("#!/bin/bash --posix" + nl)
      if (is64) {
        fw.write("SCALACLASSPATH=\"")
        fw.write((out.absolutePath +: depsPaths).mkString(":"))
        fw.write("\"" + nl + nl)

        // Setting the dynamic lib path
        fw.write("LIBRARY_PATH=\"" + ldLibraryDir64.absolutePath + "\"" + nl)
      } else {
        fw.write("if [ `uname -m` == \"x86_64\" ]; then "+nl)

          fw.write("    echo \"It appears you have compiled Leon with a 32bit virtual machine, but are now trying to run it on a 64bit architecture. This is unfortunately not supported.\"" + nl)
          fw.write("    exit -1" + nl)

        fw.write("else" + nl)

          fw.write("    SCALACLASSPATH=\"")
          fw.write((out.absolutePath +: depsPaths).mkString(":"))
          fw.write("\"" + nl)

          // Setting the dynamic lib path
          fw.write("    LIBRARY_PATH=\"" + ldLibraryDir32.absolutePath + "\"" + nl)
        fw.write("fi" + nl + nl)
      }

      // the Java command that uses sbt's local Scala to run the whole contraption.
      fw.write("LD_LIBRARY_PATH=\"$LIBRARY_PATH\" \\"+nl)
      fw.write("java -Xmx2G -Xms512M -classpath ${SCALACLASSPATH} -Dscala.home=\"")
      fw.write(scalaHomeDir)
      fw.write("\" -Dscala.usejavacp=true ")
      fw.write("scala.tools.nsc.MainGenericRunner -classpath ${SCALACLASSPATH} ")
      fw.write("leon.Main $@" + nl)
      fw.close
      scriptFile.setExecutable(true)
    } catch {
      case e => s.log.error("There was an error while generating the script file: " + e.getLocalizedMessage)
    }
  }

  object LeonProject {
    val settings = Seq(
      scriptTask,
      cleanTask
    )
  }

  lazy val root = Project(
    id = "leon",
    base = file("."),
    settings = Project.defaultSettings ++ LeonProject.settings
  ) aggregate(leonLibrary) dependsOn(leonLibrary) 

  lazy val leonLibrary = Project(id = "leon-library", base = file("./library"))

}