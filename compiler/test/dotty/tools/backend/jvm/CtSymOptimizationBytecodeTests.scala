package dotty.tools.backend.jvm

import dotty.AsmConverters
import dotty.AsmConverters.instructionsFromMethod
import dotty.tools.dotc.Compiler
import dotty.tools.dotc.config.Settings.Setting.ChoiceWithHelp
import dotty.tools.dotc.core.Contexts.{Context, ctx}
import dotty.tools.dotc.reporting.StoreReporter
import org.junit.Assert.*
import org.junit.Assume.assumeTrue
import org.junit.{Before, Test}

/** With `-release N` on a newer JDK, JDK classes are read from `ct.sym`, whose `.sig` classfiles
 *  have no method bodies. The optimizer must still work and must not inline JDK code.
 */
class CtSymOptimizationBytecodeTests extends OptimizationBytecodeTest {
  private val release = "17"

  @Before def requireCtSym(): Unit =
    assumeTrue("ct.sym is only used when the JDK is newer than -release", Runtime.version().feature() > release.toInt)

  override def initCtx = {
    val ctx = super.initCtx
    ctx.setSetting(ctx.settings.javaOutputVersion, release)
    ctx.setSetting(ctx.settings.opt, true)
    ctx.setSetting(ctx.settings.optInline, List("**")) // deliberately includes java.**
    ctx.setSetting(ctx.settings.silentWarnings, false)
    ctx.setSetting(ctx.settings.Wopt, List(ChoiceWithHelp("any-inline-failed", ""), ChoiceWithHelp("no-inline-missing-bytecode", "")))
    ctx.setReporter(new StoreReporter(null))
  }

  /** Compiles `Test` and returns its instructions per method, plus the optimizer warnings. */
  private def compile(members: String): (Map[String, List[AsmConverters.Instruction]], List[String]) = {
    given Context = initCtx
    val compiler = new Compiler
    compiler.newRun.compileFromStrings(List(s"final class Test {\n$members\n}"))

    val objectFile = ctx.platform.classPath.findClassFile("java.lang.Object")
    assertTrue(s"expected java.lang.Object from ct.sym, got $objectFile", objectFile.exists(_.name.endsWith(".sig")))

    val warnings = ctx.reporter.removeBufferedMessages.map(_.message)
    val clsNode = loadClassNode(lookupClass(ctx.settings.outputDir.value, "Test.class"))
    val methods = clsNode.methods.nn.toArray(Array.empty[org.objectweb.asm.tree.MethodNode]).toList
    (methods.map(m => m.name -> instructionsFromMethod(m)).toMap, warnings)
  }

  private def invokes(instructions: List[AsmConverters.Instruction]): List[String] =
    instructions.collect { case i: AsmConverters.Invoke => s"${i.owner}.${i.name}" }

  @Test def inlineScalaLibraryMethodsThatCallTheJdk(): Unit = {
    val (methods, warnings) = compile(
      """  def strNonEmpty(s: String): Boolean = s.nonEmpty
        |  def arrMap(xs: Array[Int]): Array[Int] = xs.map(_ + 1)
        |""".stripMargin)
    assertEquals(Nil, warnings)
    assertEquals(List("java/lang/String.isEmpty"), invokes(methods("strNonEmpty")))
    val arrMapCalls = invokes(methods("arrMap"))
    assertTrue(arrMapCalls.mkString("\n"), arrMapCalls.forall(c => !c.startsWith("scala/collection/ArrayOps") && !c.startsWith("scala/Predef")))
  }

  @Test def jdkMethodsAreNotInlined(): Unit = {
    // The heuristics select these callees (factory method, higher-order method with a function literal),
    // but `.sig` files have no bytecode to inline.
    val (methods, warnings) = compile(
      """  def boxDouble(d: Double): java.lang.Double = java.lang.Double.valueOf(d)
        |  def optMap(o: java.util.Optional[String]): java.util.Optional[Integer] = o.map(s => Integer.valueOf(s.length))
        |""".stripMargin)
    assertTrue(invokes(methods("boxDouble")).contains("java/lang/Double.valueOf"))
    assertTrue(invokes(methods("optMap")).contains("java/util/Optional.map"))
    assertEquals(warnings.mkString("\n"), 2, warnings.length)
    assertTrue(warnings.mkString("\n"), warnings.forall(_.contains("does not have any instructions")))
  }
}
