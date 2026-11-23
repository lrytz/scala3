/*
 * Scala (https://www.scala-lang.org)
 *
 * Copyright EPFL and Lightbend, Inc. dba Akka
 *
 * Licensed under Apache License 2.0
 * (http://www.apache.org/licenses/LICENSE-2.0).
 *
 * See the NOTICE file distributed with this work for
 * additional information regarding copyright ownership.
 */

package scala
package collection
package mutable

import scala.language.`2.13`
import language.experimental.captureChecking
import scala.annotation.nowarn
import scala.collection.Stepper.EfficientSplit
import scala.collection.generic.{CommonErrors, DefaultSerializable}
import scala.reflect.ClassTag
import scala.runtime.PStatics.VM_MaxArraySize

/** An implementation of a double-ended queue that internally uses a resizable circular buffer.
  *
  *  Append, prepend, removeHead, removeLast and random-access (indexed-lookup and indexed-replacement)
  *  take amortized constant time. In general, removals and insertions at i-th index are O(min(i, n-i))
  *  and thus insertions and removals from end/beginning are fast.
  *
  *  @note Subclasses *must* override the `ofArray` protected method to return a more specific type.
  *
  *  @tparam A  the type of this ArrayDeque's elements.
  *
  *  @define Coll `mutable.ArrayDeque`
  *  @define coll array deque
  *  @define orderDependent
  *  @define orderDependentFold
  *  @define mayNotTerminateInf
  *  @define willNotTerminateInf
  */
class ArrayDeque[A] protected (
    protected var array: Array[AnyRef | Null],
    private[ArrayDeque] var start: Int,
    end: Int
) extends AbstractBuffer[A]
    with IndexedBuffer[A]
    with IndexedSeqOps[A, ArrayDeque, ArrayDeque[A]]
    with StrictOptimizedSeqOps[A, ArrayDeque, ArrayDeque[A]]
    with IterableFactoryDefaults[A, ArrayDeque]
    with ArrayDequeOps[A, ArrayDeque, ArrayDeque[A]]
    with Cloneable[ArrayDeque[A]]
    with DefaultSerializable {

  // The elements occupy `len` slots of `array` starting at `start`, wrapping around at the end of `array`.
  // Storing the length rather than an end index lets the deque fill its array completely, so the
  // capacity need not exceed the length; and the capacity need not be a power of two.
  private var len: Int = 0

  {
    // `end == array.length` (with `start == 0`) denotes a full array
    requireBounds(idx = start, until = array.length)
    requireBounds(idx = end, until = array.length + 1)
    len = if (end >= start) end - start else end - start + array.length
  }

  def this(initialSize: Int = ArrayDeque.DefaultInitialSize) = this(ArrayDeque.alloc(initialSize), start = 0, end = 0)

  override def knownSize: Int = len

  // No-Op override to allow for more efficient stepper in a minor release.
  override def stepper[S <: Stepper[?]](implicit shape: StepperShape[A, S]): S & EfficientSplit = super.stepper(using shape)

  def apply(idx: Int): A = {
    requireBounds(idx, len)
    _get(idx)
  }

  def update(idx: Int, elem: A): Unit = {
    requireBounds(idx, len)
    _set(idx, elem)
  }

  def addOne(elem: A): this.type = {
    val n = len
    if (n == array.length) grow(n + 1)
    len = n + 1
    array(start_+(n)) = elem.asInstanceOf[AnyRef]
    this
  }

  def prepend(elem: A): this.type = {
    val n = len
    if (n == array.length) grow(n + 1)
    start = start_-(1)
    len = n + 1
    array(start) = elem.asInstanceOf[AnyRef]
    this
  }

  override def foreach[U](f: A => U): Unit = {
    val n = len
    var i = 0
    while (i < n) {
      f(this(i))
      i += 1
    }
  }

  override def iterator: Iterator[A] = new ArrayDeque.ArrayDequeIterator(this)

  override def prependAll(elems: IterableOnce[A]^): this.type = {
    val it = elems.iterator
    if (it.nonEmpty) {
      val n = len
      // The following code resizes the current collection at most once and traverses elems at most twice
      elems.knownSize match {
        // Size is too expensive to compute AND we can traverse it only once - can't do much but retry with an IndexedSeq
        case srcLength if srcLength < 0 => prependAll(it.to(IndexedSeq: Factory[A, IndexedSeq[A]] /* type ascription needed by Dotty */))

        case srcLength =>
          val finalLength = srcLength + n
          val newCapacity = ArrayBuffer.resizeUp(array.length, finalLength)
          if (newCapacity >= 0) {
            // We need to resize to hold everything, might as well resize and memcopy upfront
            val array2 = new Array[AnyRef | Null](newCapacity)
            @annotation.unused val copied = it.copyToArray(array2.asInstanceOf[Array[A]], 0, srcLength)
            //assert(copied == srcLength)
            copySliceToArray(srcStart = 0, dest = array2, destStart = srcLength, maxItems = n)
            setArray(array2, finalLength)
          } else {
            // Move start back by srcLength and fill the gap
            start = start_-(srcLength)
            len = finalLength
            var i = 0
            while (i < srcLength) {
              _set(i, it.next())
              i += 1
            }
          }
      }
    }
    this
  }

  override def addAll(elems: IterableOnce[A]^): this.type = {
    elems.knownSize match {
      case srcLength if srcLength > 0 =>
        ensureSize(srcLength + len)
        val n = len
        val pos = start_+(n)
        if (srcLength <= array.length - pos) {
          // The free space is contiguous: copy in bulk, which is an `arraycopy` for array-backed sources
          len = n + IterableOnce.copyElemsToArray(elems, array.asInstanceOf[Array[Any]], pos, srcLength)
        } else {
          val it = elems.iterator
          var i = n
          while (it.hasNext) {
            array(start_+(i)) = it.next().asInstanceOf[AnyRef]
            i += 1
          }
          len = i
        }
      case _ => super.addAll(elems)
    }
    this
  }

  def insert(idx: Int, elem: A): Unit = {
    requireBounds(idx, len+1)
    val n = len
    if (idx == 0) {
      prepend(elem)
    } else if (idx == n) {
      addOne(elem)
    } else {
      val finalLength = n + 1
      if (n == array.length) {
        val array2 = new Array[AnyRef | Null](ArrayBuffer.resizeUp(array.length, finalLength))
        copySliceToArray(srcStart = 0, dest = array2, destStart = 0, maxItems = idx)
        array2(idx) = elem.asInstanceOf[AnyRef]
        copySliceToArray(srcStart = idx, dest = array2, destStart = idx + 1, maxItems = n)
        setArray(array2, finalLength)
      } else if (n <= idx * 2) { // Cheaper to shift the suffix right
        len = finalLength
        var i = n - 1
        while(i >= idx) {
          _set(i + 1, _get(i))
          i -= 1
        }
        _set(idx, elem)
      } else { // Cheaper to shift the prefix left
        start = start_-(1)
        len = finalLength
        var i = 0
        while(i < idx) {
          _set(i, _get(i + 1))
          i += 1
        }
        _set(idx, elem)
      }
    }
  }

  def insertAll(idx: Int, elems: IterableOnce[A]^): Unit = {
    requireBounds(idx, len+1)
    val n = len
    if (idx == 0) {
      prependAll(elems)
    } else if (idx == n) {
      addAll(elems)
    } else {
      // Get both an iterator and the length of the source (by copying the source to an IndexedSeq if needed)
      val (it, srcLength) = {
        val _srcLength = elems.knownSize
        if (_srcLength >= 0) (elems.iterator, _srcLength)
        else {
          val indexed = IndexedSeq.from(elems)
          (indexed.iterator, indexed.size)
        }
      }
      if (it.nonEmpty) {
        val finalLength = srcLength + n
        val newCapacity = ArrayBuffer.resizeUp(array.length, finalLength)
        // Either we resize right away or move prefix left or suffix right
        if (newCapacity >= 0) {
          val array2 = new Array[AnyRef | Null](newCapacity)
          copySliceToArray(srcStart = 0, dest = array2, destStart = 0, maxItems = idx)
          @annotation.unused val copied = it.copyToArray(array2.asInstanceOf[Array[A]], idx, srcLength)
          //assert(copied == srcLength)
          copySliceToArray(srcStart = idx, dest = array2, destStart = idx + srcLength, maxItems = n)
          setArray(array2, finalLength)
        } else if (2*idx >= n) { // Cheaper to shift the suffix right
          len = finalLength
          var i = n - 1
          while(i >= idx) {
            _set(i + srcLength, _get(i))
            i -= 1
          }
          i = idx
          while(it.hasNext) {
            _set(i, it.next())
            i += 1
          }
        } else {  // Cheaper to shift prefix left
          start = start_-(srcLength)
          len = finalLength
          var i = 0
          while(i < idx) {
            _set(i, _get(i + srcLength))
            i += 1
          }
          while(it.hasNext) {
            _set(i, it.next())
            i += 1
          }
        }
      }
    }
  }

  def remove(idx: Int, count: Int): Unit = {
    if (count > 0) {
      requireBounds(idx, len)
      val n = len
      val removals = Math.min(n - idx, count)
      val finalLength = n - removals
      val suffixStart = idx + removals
      // If we know we can resize after removing, do it right away using arrayCopy
      // Else, choose the shorter: either move the prefix (0 until idx) right OR the suffix (idx+removals until n) left
      if (shouldShrink(finalLength)) {
        val array2 = new Array[AnyRef | Null](shrunkCapacity(finalLength))
        copySliceToArray(srcStart = 0, dest = array2, destStart = 0, maxItems = idx)
        copySliceToArray(srcStart = suffixStart, dest = array2, destStart = idx, maxItems = n)
        setArray(array2, finalLength)
      } else if (2*idx <= finalLength) { // Cheaper to move the prefix right
        var i = suffixStart - 1
        while(i >= removals) {
          _set(i, _get(i - removals))
          i -= 1
        }
        while(i >= 0) {
          _set(i, null.asInstanceOf[A])
          i -= 1
        }
        start = start_+(removals)
        len = finalLength
      } else {  // Cheaper to move the suffix left
        var i = idx
        while(i < finalLength) {
          _set(i, _get(i + removals))
          i += 1
        }
        while(i < n) {
          _set(i, null.asInstanceOf[A])
          i += 1
        }
        len = finalLength
      }
    } else {
      require(count == 0, s"removing negative number of elements: $count")
    }
  }

  def remove(idx: Int): A = {
    val elem = this(idx)
    remove(idx, 1)
    elem
  }

  override def subtractOne(elem: A): this.type = {
    val idx = indexOf(elem)
    if (idx >= 0) remove(idx, 1) //TODO: SeqOps should be fluent API
    this
  }

  /**
    *
    * @param resizeInternalRepr If this is set, resize the internal representation to reclaim space once in a while
    * @return
    */
  def removeHeadOption(resizeInternalRepr: Boolean = false): Option[A] =
    if (isEmpty) None else Some(removeHeadAssumingNonEmpty(resizeInternalRepr))

  /**
    * Unsafely remove the first element (throws exception when empty)
    * See also removeHeadOption()
    *
    * @param resizeInternalRepr If this is set, resize the internal representation to reclaim space once in a while
    * @throws NoSuchElementException when empty
    * @return
    */
  def removeHead(resizeInternalRepr: Boolean = false): A =
    if (isEmpty) throw new NoSuchElementException(s"empty collection") else removeHeadAssumingNonEmpty(resizeInternalRepr)

  @inline private def removeHeadAssumingNonEmpty(resizeInternalRepr: Boolean = false): A = {
    val elem = array(start)
    array(start) = null
    start = start_+(1)
    len -= 1
    if (resizeInternalRepr) shrinkIfSparse()
    elem.asInstanceOf[A]
  }

  /**
    *
    * @param resizeInternalRepr If this is set, resize the internal representation to reclaim space once in a while
    * @return
    */
  def removeLastOption(resizeInternalRepr: Boolean = false): Option[A] =
    if (isEmpty) None else Some(removeLastAssumingNonEmpty(resizeInternalRepr))

  /**
    * Unsafely remove the last element (throws exception when empty)
    * See also removeLastOption()
    *
    * @param resizeInternalRepr If this is set, resize the internal representation to reclaim space once in a while
    * @throws NoSuchElementException when empty
    * @return
    */
  def removeLast(resizeInternalRepr: Boolean = false): A =
    if (isEmpty) throw new NoSuchElementException(s"empty collection") else removeLastAssumingNonEmpty(resizeInternalRepr)

  @`inline` private def removeLastAssumingNonEmpty(resizeInternalRepr: Boolean = false): A = {
    val last = start_+(len - 1)
    val elem = array(last)
    array(last) = null
    len -= 1
    if (resizeInternalRepr) shrinkIfSparse()
    elem.asInstanceOf[A]
  }

  /**
    * Removes all elements from this collection and returns the elements while emptying this data structure.
    * @return
    */
  def removeAll(): scala.collection.immutable.Seq[A] = {
    val elems = scala.collection.immutable.Seq.newBuilder[A]
    elems.sizeHint(length)
    while(nonEmpty) {
      elems += removeHeadAssumingNonEmpty()
    }
    elems.result()
  }

  /**
    * Removes all elements from this collection and returns the elements in reverse while emptying this data structure.
    * @return
    */
  def removeAllReverse(): scala.collection.immutable.Seq[A] = {
    val elems = scala.collection.immutable.Seq.newBuilder[A]
    elems.sizeHint(length)
    while(nonEmpty) {
      elems += removeLastAssumingNonEmpty()
    }
    elems.result()
  }

  /**
    * Returns and removes all elements from the left of this queue which satisfy the given predicate
    *
    *  @param f   the predicate used for choosing elements
    *  @return
    */
  def removeHeadWhile(f: A => Boolean): scala.collection.immutable.Seq[A] = {
    val elems = scala.collection.immutable.Seq.newBuilder[A]
    while(headOption.exists(f)) {
      elems += removeHeadAssumingNonEmpty()
    }
    elems.result()
  }

  /**
    * Returns and removes all elements from the right of this queue which satisfy the given predicate
    *
    *  @param f   the predicate used for choosing elements
    *  @return
    */
  def removeLastWhile(f: A => Boolean): scala.collection.immutable.Seq[A] = {
    val elems = scala.collection.immutable.Seq.newBuilder[A]
    while(lastOption.exists(f)) {
      elems += removeLastAssumingNonEmpty()
    }
    elems.result()
  }

  /** Returns the first element which satisfies the given predicate after or at some start index
    * and removes this element from the collections
    *
    *  @param p   the predicate used for choosing the first element
    *  @param from the start index
    *  @return the first element of the queue for which p yields true
    */
  def removeFirst(p: A => Boolean, from: Int = 0): Option[A] = {
    val i = indexWhere(p, from)
    if (i < 0) None else Some(remove(i))
  }

  /** Returns all elements in this collection which satisfy the given predicate
    * and removes those elements from this collections.
    *
    *  @param p   the predicate used for choosing elements
    *  @return    a sequence of all elements in the queue for which
    *             p yields true.
    */
  def removeAll(p: A => Boolean): scala.collection.immutable.Seq[A] = {
    val res = scala.collection.immutable.Seq.newBuilder[A]
    var i, j = 0
    while (i < size) {
      if (p(this(i))) {
        res += this(i)
      } else {
        if (i != j) {
          this(j) = this(i)
        }
        j += 1
      }
      i += 1
    }
    if (i != j) takeInPlace(j)
    res.result()
  }

  /** Ensures the internal array can hold at least `hint` elements. */
  def ensureSize(hint: Int): Unit = if (hint > array.length) grow(hint)

  def length = len

  override def isEmpty = len == 0

  override protected def klone(): ArrayDeque[A] =
    new ArrayDeque(copySliceToArray(srcStart = 0, dest = new Array[AnyRef | Null](array.length), destStart = 0, maxItems = len), start = 0, end = len)

  override def iterableFactory: SeqFactory[ArrayDeque] = ArrayDeque

  /**
    * Note: This does not actually resize the internal representation.
    * See clearAndShrink if you want to also resize internally
    */
  def clear(): Unit = {
    if (nonEmpty) {
      val untilArrayEnd = array.length - start
      if (len <= untilArrayEnd) {
        java.util.Arrays.fill(array, start, start + len, null)
      } else {
        java.util.Arrays.fill(array, start, array.length, null)
        java.util.Arrays.fill(array, 0, len - untilArrayEnd, null)
      }
      start = 0
      len = 0
    }
  }

  /**
    * Clears this buffer and shrinks to @param size
    *
    * @param size
    * @return
    */
  def clearAndShrink(size: Int = ArrayDeque.DefaultInitialSize): this.type = {
    setArray(ArrayDeque.alloc(size), 0)
    this
  }

  protected def ofArray(array: Array[AnyRef | Null], end: Int): ArrayDeque[A] =
    new ArrayDeque[A](array, start = 0, end)

  override def copyToArray[B >: A](dest: Array[B], destStart: Int, len: Int): Int = {
    val copied = IterableOnce.elemsToCopyToArray(length, dest.length, destStart, len)
    if (copied > 0) {
      copySliceToArray(srcStart = 0, dest = dest, destStart = destStart, maxItems = len)
    }
    copied
  }

  override def toArray[B >: A: ClassTag]: Array[B] =
    copySliceToArray(srcStart = 0, dest = new Array[B](length), destStart = 0, maxItems = length)

  /**
    * Trims the capacity of this ArrayDeque's instance to be the current size
    */
  def trimToSize(): Unit = if (len < array.length) resize(len)

  // Index arithmetic modulo `array.length`. Written as in `java.util.ArrayDeque` to remain correct
  // when `start + idx` overflows.
  @inline protected def start_+(idx: Int) = { val i = start + idx; if (i - array.length >= 0) i - array.length else i }
  @inline private def start_-(idx: Int) = { val i = start - idx; if (i < 0) i + array.length else i }

  // Assumes that 0 <= len < array.length!
  @inline private def shouldShrink(len: Int) = {
    // To avoid allocation churn, only shrink when array is large
    // and less than 2/5 filled.
    array.length > ArrayDeque.StableSize && array.length - len - (len >> 1) > len
  }

  // Assumes that 0 <= len.
  @inline private def canShrink(len: Int) = {
    array.length > ArrayDeque.DefaultInitialSize && array.length - len > len
  }

  // Leaves room to grow by half, so that shrinking again needs a substantial number of removals
  @inline private def shrunkCapacity(len: Int) = Math.max(len + (len >> 1), ArrayDeque.DefaultInitialSize)

  private def shrinkIfSparse(): Unit = if (canShrink(len)) resize(shrunkCapacity(len))

  @inline private def _get(idx: Int): A = array(start_+(idx)).asInstanceOf[A]

  @inline private def _set(idx: Int, elem: A) = array(start_+(idx)) = elem.asInstanceOf[AnyRef]

  private def setArray(array: Array[AnyRef | Null], len: Int): Unit = {
    this.array = array
    this.start = 0
    this.len = len
  }

  // Grows the array to hold at least `minCapacity` elements, at least doubling it.
  private def grow(minCapacity: Int): Unit = resize(ArrayBuffer.resizeUp(array.length, minCapacity))

  // Assumes that `len <= capacity`.
  private def resize(capacity: Int): Unit =
    setArray(copySliceToArray(srcStart = 0, dest = ArrayDeque.alloc(capacity), destStart = 0, maxItems = len), len)

  @nowarn("""cat=deprecation&origin=scala\.collection\.Iterable\.stringPrefix""")
  override protected def stringPrefix = "ArrayDeque"
}

/**
  * $factoryInfo
  * @define coll array deque
  * @define Coll `ArrayDeque`
  */
@SerialVersionUID(3L)
object ArrayDeque extends StrictOptimizedSeqFactory[ArrayDeque] {

  def from[B](coll: collection.IterableOnce[B]^): ArrayDeque[B] = {
    val s = coll.knownSize
    if (s >= 0) {
      val array = alloc(s)
      val actual = IterableOnce.copyElemsToArray(coll, array.asInstanceOf[Array[Any]])
      if (actual != s) throw new IllegalStateException(s"Copied $actual of $s")
      new ArrayDeque[B](array, start = 0, end = s)
    } else new ArrayDeque[B]() ++= coll
  }

  def newBuilder[A]: Builder[A, ArrayDeque[A]] =
    new GrowableBuilder[A, ArrayDeque[A]](empty) {
      override def sizeHint(size: Int): Unit = {
        elems.ensureSize(size)
      }
    }

  def empty[A]: ArrayDeque[A] = new ArrayDeque[A]()

  // Like `IndexedSeqView`'s iterator, but without the indirection through a view
  private final class ArrayDequeIterator[A](self: ArrayDeque[A]) extends AbstractIterator[A] with Serializable {
    private var current = 0
    private var remainder = self.length
    override def knownSize: Int = remainder
    def hasNext: Boolean = remainder > 0
    def next(): A =
      if (remainder > 0) {
        val r = self(current)
        current += 1
        remainder -= 1
        r
      } else Iterator.empty.next()

    override def drop(n: Int): Iterator[A]^{this} = {
      if (n > 0) {
        current += n
        remainder = Math.max(0, remainder - n)
      }
      this
    }

    override protected def sliceIterator(from: Int, until: Int): Iterator[A]^{this} = {
      def formatRange(value: Int): Int = if (value < 0) 0 else if (value > remainder) remainder else value
      val formatFrom = formatRange(from)
      val formatUntil = formatRange(until)
      remainder = Math.max(0, formatUntil - formatFrom)
      current = current + formatFrom
      this
    }
  }

  final val DefaultInitialSize = 16

  /**
    * We try to not repeatedly resize arrays smaller than this
    */
  private[ArrayDeque] final val StableSize = 128

  /** Allocates an array for `len` elements. The array is never empty, so that index arithmetic modulo its length is defined. */
  private[mutable] def alloc(len: Int) = {
    require(len >= 0, s"Non-negative array size required")
    require(len <= VM_MaxArraySize, s"ArrayDeque too big - cannot allocate ArrayDeque of length $len")
    new Array[AnyRef | Null](Math.max(len, 1))
  }
}

transparent trait ArrayDequeOps[A, +CC[_] <: caps.Pure, +C <: AnyRef] extends StrictOptimizedSeqOps[A, CC, C] {
  protected def array: Array[AnyRef | Null]

  final override def clone(): C = klone()

  protected def klone(): C

  protected def ofArray(array: Array[AnyRef | Null], end: Int): C

  protected def start_+(idx: Int): Int

  @inline protected final def requireBounds(idx: Int, until: Int = length): Unit =
    if (idx < 0 || idx >= until)
      throw CommonErrors.indexOutOfBounds(index = idx, max = until - 1)

  /** This is a more general version of copyToArray - this also accepts a srcStart unlike copyToArray
   *  This copies maxItems elements from this collections srcStart to dest's destStart
   *  If we reach the end of either collection before we could copy maxItems, we simply stop copying
   *
   *  @param dest
   *  @param srcStart
   *  @param destStart
   *  @param maxItems
   *  @return the `dest` array, after the copied elements have been written into it
   */
  def copySliceToArray(srcStart: Int, dest: Array[?], destStart: Int, maxItems: Int): dest.type = {
    requireBounds(destStart, dest.length+1)
    val toCopy = Math.min(maxItems, Math.min(length - srcStart, dest.length - destStart))
    if (toCopy > 0) {
      requireBounds(srcStart)
      val startIdx = start_+(srcStart)
      val block1 = Math.min(toCopy, array.length - startIdx)
      Array.copy(src = array, srcPos = startIdx, dest = dest, destPos = destStart, length = block1)
      val block2 = toCopy - block1
      if (block2 > 0) Array.copy(src = array, srcPos = 0, dest = dest, destPos = destStart + block1, length = block2)
    }
    dest
  }

  override def reverse: C = {
    val n = length
    val arr = ArrayDeque.alloc(n)
    var i = 0
    while(i < n) {
      arr(i) = this(n - i - 1).asInstanceOf[AnyRef]
      i += 1
    }
    ofArray(arr, n)
  }

  override def slice(from: Int, until: Int): C = {
    val n = length
    val left = Math.max(0, Math.min(n, from))
    val right = Math.max(0, Math.min(n, until))
    val len = right - left
    if (len <= 0) {
      empty
    } else if (len >= n) {
      klone()
    } else {
      val array2 = copySliceToArray(srcStart = left, dest = ArrayDeque.alloc(len), destStart = 0, maxItems = len)
      ofArray(array2, len)
    }
  }

  override def sliding(@deprecatedName("window") size: Int, step: Int): Iterator[C] =
    super.sliding(size = size, step = step)

  override def grouped(n: Int): Iterator[C] = sliding(n, n)
}
