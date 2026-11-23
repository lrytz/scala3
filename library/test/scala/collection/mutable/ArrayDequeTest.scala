package scala.collection.mutable

import org.junit.Test
import org.junit.Assert.*

import scala.annotation.nowarn
import scala.collection.SeqFactory
import scala.collection.immutable.List
import tools.AssertUtil.assertThrows

class ArrayDequeTest {

  @Test
  def apply: Unit = {
    val buffer = ArrayDeque.empty[Int]
    val standard = ArrayBuffer.empty[Int]

    def apply[U](f: Buffer[Int] => U) = {
      //println(s"Before: [buffer1=${buffer}; buffer2=${buffer2}]")
      assertEquals(f(standard), f(buffer))
      assertEquals(standard, buffer)
      assertEquals(standard.reverse, buffer.reverse)
    }

    apply(_.+=(1, 2, 3, 4, 5)): @nowarn("cat=deprecation")
    apply(_.prepend(6).prepend(7).prepend(8))
    apply(_.dropInPlace(2))
    apply(_.dropRightInPlace(3))
    apply(_.insert(2, -3))
    apply(_.insertAll(0, collection.Seq(9, 10, 11)))
    apply(_.insertAll(1, collection.Seq(12, 13)))
    apply(_.insertAll(0, collection.Seq(23, 24)))
    apply(_ ++= Seq(25, 26))
    apply(_.insertAll(3, collection.IndexedSeq(18, 33)))
    apply(_.remove(2))
    apply(_.prependAll(collection.Seq(14, 15, 16, 17)))
    apply(_.remove(1, 5))
    apply(_.prependAll(Seq.tabulate(100)(identity)))
    apply(b => b.insertAll(b.length - 5, collection.Seq.tabulate(10)(identity)))
    buffer.trimToSize()
    apply(_.addAll(collection.Seq.tabulate(100)(identity)))
    apply(_.addAll(collection.Iterator.tabulate(100)(identity)))
    apply(_.addAll(collection.immutable.Vector.tabulate(10)(identity)))

    (-100 to 100) foreach {i =>
      assertEquals(standard.splitAt(i), buffer.splitAt(i))
    }

    for {
      i <- -100 to 100
      j <- -100 to 100
    } {
      assertEquals(standard.slice(i, j), buffer.slice(i, j))
      if (i > 0 && j > 0) assertEquals(List.from(standard.sliding(i, j)), List.from(buffer.sliding(i, j)))
    }
  }

  @Test
  def queueBounds(): Unit = {
    import scala.collection.mutable.Queue

    val xs = Queue.empty[Int]
    assertEquals("Queue()", xs.toString)

    val a = xs.toArray
    assertEquals(0, a.length)

    xs.insert(0, 0)
    assertEquals(Queue(0), xs)
  }

  @Test
  def copyToArrayOutOfBounds(): Unit = {
    val target = Array[Int]()
    assertEquals(0, collection.mutable.ArrayDeque(1, 2).copyToArray(target, 1, 0))
  }

  @Test
  def insertsWhenResizeIsNeeded(): Unit = {
    val arrayDeque = ArrayDeque.from(Array.range(0, 15))
    arrayDeque.insert(1, -1)
    assertEquals(ArrayDeque(0, -1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14), arrayDeque)
  }

  @Test
  def insertAll(): Unit = {
    var a = ArrayDeque(0, 1)
    a.insertAll(1, Seq(2))
    assertEquals(ArrayDeque(0, 2, 1), a)
    a = ArrayDeque(0, 1)
    a.insertAll(2, Seq(2))
    assertEquals(ArrayDeque(0, 1, 2), a)
    var q = Queue(0, 1)
    q.patchInPlace(1, Seq(2), 0)
    assertEquals(Queue(0, 2, 1), q)
    q = Queue(0, 1)
    q.patchInPlace(2, Seq(2), 0)
    assertEquals(Queue(0, 1, 2), q)
  }

  @Test
  def sliding(): Unit = ArrayDequeTest.genericSlidingTest(ArrayDeque, "ArrayDeque")


  class PeekingArrayDeque[C](initialSize: Int = ArrayDeque.DefaultInitialSize) extends ArrayDeque[C](initialSize) {
    def capacity = array.length
  }

  @Test
  def trimToSize(): Unit = {
    val a = new PeekingArrayDeque().addAll(0 to 255)

    a.trimToSize()  // Can't shrink
    assertEquals(256, a.capacity)
    a.remove(0)
    assertEquals(256, a.capacity)
    a.trimToSize()
    assertEquals(255, a.capacity)
  }

  @Test
  def fillsArrayCompletely(): Unit = {
    val a = new PeekingArrayDeque[Int](5)
    a ++= Seq(2, 3, 4)
    a.prepend(1).prepend(0) // wraps around the end of the array
    assertEquals(5, a.capacity)
    assertEquals(ArrayDeque(0, 1, 2, 3, 4), a)
    assertEquals(4, a.remove(4))
    a.insert(1, 10)
    assertEquals(ArrayDeque(0, 10, 1, 2, 3), a)
    assertEquals(5, a.capacity)
    assertEquals(List(0, 10, 1, 2, 3), a.clone().toList)
    a += 5
    assertEquals(ArrayDeque(0, 10, 1, 2, 3, 5), a)
    assertEquals(16, a.capacity)
  }

  @Test
  def sameAsArrayBuffer(): Unit = {
    val rnd = new scala.util.Random(42)
    for (round <- 0 until 2000) {
      val d = new PeekingArrayDeque[Int](rnd.nextInt(5))
      val b = ArrayBuffer.empty[Int]
      val ops = ArrayBuffer.empty[String]
      def step(name: String)(f: Buffer[Int] => Any): Unit = {
        ops += name
        val expected = f(b)
        val actual = f(d)
        assertEquals(s"$name after ${ops.mkString("; ")}", expected, actual)
        assertEquals(s"after ${ops.mkString("; ")}", b, d)
        assertTrue(d.length <= d.capacity)
      }
      for (_ <- 0 until (if (round % 10 == 0) 600 else 60)) {
        val n = b.length
        val x = rnd.nextInt(100)
        val xs = List.fill(rnd.nextInt(6))(rnd.nextInt(100))
        rnd.nextInt(12) match {
          case 0 | 1 | 2 => step(s"+= $x")(_ += x)
          case 3 | 4 | 5 => step(s"prepend $x")(_.prepend(x))
          case 6 => val i = rnd.nextInt(n + 1); step(s"insert $i $x")(_.insert(i, x))
          case 7 => val i = rnd.nextInt(n + 1); step(s"insertAll $i $xs")(_.insertAll(i, if (rnd.nextBoolean()) xs else xs.iterator))
          case 8 => step(s"prependAll $xs")(_.prependAll(xs))
          case 9 => step(s"addAll $xs")(_.addAll(if (rnd.nextBoolean()) xs.toVector else xs.iterator))
          case 10 => if (n > 0) { val i = rnd.nextInt(n); val c = rnd.nextInt(n - i + 1); step(s"remove $i $c")(_.remove(i, c)) }
          case 11 => if (n > 0) { val r = rnd.nextBoolean(); if (rnd.nextBoolean()) step(s"removeHead $r")(bb => if (bb eq d) d.removeHead(r) else b.remove(0)) else step(s"removeLast $r")(bb => if (bb eq d) d.removeLast(r) else b.remove(n - 1)) }
        }
      }
    }
  }

  @Test def `head of empty throws NoSuchElement`: Unit =
    assertThrows[NoSuchElementException](ArrayDeque.empty[Int].head, _.endsWith("head of empty ArrayDeque"))

  @Test def `last of empty throws NoSuchElement`: Unit =
    assertThrows[NoSuchElementException](ArrayDeque.empty[Int].last, _.endsWith("last of empty ArrayDeque"))

  @Test def `sliding throws on shrink`: Unit = {
    val sut = ArrayDeque.from(1 to 10)
    val it = sut.sliding(size = 2, step = 1)
    assertTrue(it.hasNext)
    assertEquals(2, it.next().size)
    sut.clear()
    assertThrows[java.util.ConcurrentModificationException](it.hasNext)
  }

  @Test def `sliding throws on grow`: Unit = {
    val sut = ArrayDeque.from(1 to 10)
    val it = sut.sliding(size = 2, step = 1)
    assertTrue(it.hasNext)
    assertEquals(2, it.next().size)
    sut.addOne(100)
    assertThrows[java.util.ConcurrentModificationException](it.hasNext)
  }
}

object ArrayDequeTest {

  // tests scala/bug#11047
  def genericSlidingTest(factory: SeqFactory[ArrayDeque], collectionName: String): Unit = {
    for (i <- 0 to 40; j <- 1 to 40; k <- 1 to 40) {
      val range = 0 until i
      val other = factory.from(range)
      val iterableSliding = range.sliding(j, k).to(Seq)
      val otherSliding = other.sliding(j, k).to(Seq)
      assert(iterableSliding == otherSliding,
        s"""Iterable.from($range)).sliding($j,$k) differs from $collectionName.from($range)).sliding($j,$k)
            |Iterable yielded: $iterableSliding
            |$collectionName yielded: $otherSliding
            |""".stripMargin
      )
    }

    // scala/bug#11440
    assertEquals(0, factory.empty[Int].sliding(1).size)

    // no general mutation check
    locally {
      val sut = factory.from(1 to 2)
      val it = sut.sliding(size = 2, step = 1)
      sut(1) = 100
      assertTrue(it.hasNext)
      assertEquals(1, it.size)
    }
  }
}
