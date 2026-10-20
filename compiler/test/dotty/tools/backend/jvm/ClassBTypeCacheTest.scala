package dotty.tools.backend.jvm

import dotty.tools.backend.jvm.opt.{ClassNotFound, NoClassBTypeInfo}
import org.junit.Assert.*
import org.junit.Test

class ClassBTypeCacheTest {
  @Test def failedInitializationIsRemembered(): Unit = {
    val cache = new ClassBType.Cache
    val warning = NoClassBTypeInfo(ClassNotFound("p/Missing"))
    assertEquals(Left(warning), cache("p/Missing")(_ => Left(warning)))
    assertEquals(Left(warning), cache("p/Missing")(_ => { fail("initialized twice"); Left(warning) }))
    assertEquals(None, cache.previouslyConstructedClassBType("p/Missing"))
  }
}
