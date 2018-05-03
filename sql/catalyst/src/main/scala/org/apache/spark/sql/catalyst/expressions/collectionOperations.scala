/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.spark.sql.catalyst.expressions

import java.util.Comparator

import org.apache.spark.sql.catalyst.InternalRow
import org.apache.spark.sql.catalyst.analysis.TypeCheckResult
import org.apache.spark.sql.catalyst.expressions.codegen._
import org.apache.spark.sql.catalyst.util.{ArrayData, GenericArrayData, MapData, TypeUtils}
import org.apache.spark.sql.types._
import org.apache.spark.unsafe.Platform
import org.apache.spark.unsafe.array.ByteArrayMethods
import org.apache.spark.unsafe.types.{ByteArray, UTF8String}
import org.apache.spark.util.collection.OpenHashSet

/**
 * Given an array or map, returns its size. Returns -1 if null.
 */
@ExpressionDescription(
  usage = "_FUNC_(expr) - Returns the size of an array or a map. Returns -1 if null.",
  examples = """
    Examples:
      > SELECT _FUNC_(array('b', 'd', 'c', 'a'));
       4
  """)
case class Size(child: Expression) extends UnaryExpression with ExpectsInputTypes {
  override def dataType: DataType = IntegerType
  override def inputTypes: Seq[AbstractDataType] = Seq(TypeCollection(ArrayType, MapType))
  override def nullable: Boolean = false

  override def eval(input: InternalRow): Any = {
    val value = child.eval(input)
    if (value == null) {
      -1
    } else child.dataType match {
      case _: ArrayType => value.asInstanceOf[ArrayData].numElements()
      case _: MapType => value.asInstanceOf[MapData].numElements()
    }
  }

  override def doGenCode(ctx: CodegenContext, ev: ExprCode): ExprCode = {
    val childGen = child.genCode(ctx)
    ev.copy(code = s"""
      boolean ${ev.isNull} = false;
      ${childGen.code}
      ${CodeGenerator.javaType(dataType)} ${ev.value} = ${childGen.isNull} ? -1 :
        (${childGen.value}).numElements();""", isNull = FalseLiteral)
  }
}

/**
 * Returns an unordered array containing the keys of the map.
 */
@ExpressionDescription(
  usage = "_FUNC_(map) - Returns an unordered array containing the keys of the map.",
  examples = """
    Examples:
      > SELECT _FUNC_(map(1, 'a', 2, 'b'));
       [1,2]
  """)
case class MapKeys(child: Expression)
  extends UnaryExpression with ExpectsInputTypes {

  override def inputTypes: Seq[AbstractDataType] = Seq(MapType)

  override def dataType: DataType = ArrayType(child.dataType.asInstanceOf[MapType].keyType)

  override def nullSafeEval(map: Any): Any = {
    map.asInstanceOf[MapData].keyArray()
  }

  override def doGenCode(ctx: CodegenContext, ev: ExprCode): ExprCode = {
    nullSafeCodeGen(ctx, ev, c => s"${ev.value} = ($c).keyArray();")
  }

  override def prettyName: String = "map_keys"
}

/**
 * Returns an unordered array containing the values of the map.
 */
@ExpressionDescription(
  usage = "_FUNC_(map) - Returns an unordered array containing the values of the map.",
  examples = """
    Examples:
      > SELECT _FUNC_(map(1, 'a', 2, 'b'));
       ["a","b"]
  """)
case class MapValues(child: Expression)
  extends UnaryExpression with ExpectsInputTypes {

  override def inputTypes: Seq[AbstractDataType] = Seq(MapType)

  override def dataType: DataType = ArrayType(child.dataType.asInstanceOf[MapType].valueType)

  override def nullSafeEval(map: Any): Any = {
    map.asInstanceOf[MapData].valueArray()
  }

  override def doGenCode(ctx: CodegenContext, ev: ExprCode): ExprCode = {
    nullSafeCodeGen(ctx, ev, c => s"${ev.value} = ($c).valueArray();")
  }

  override def prettyName: String = "map_values"
}

/**
 * Sorts the input array in ascending / descending order according to the natural ordering of
 * the array elements and returns it.
 */
// scalastyle:off line.size.limit
@ExpressionDescription(
  usage = "_FUNC_(array[, ascendingOrder]) - Sorts the input array in ascending or descending order according to the natural ordering of the array elements.",
  examples = """
    Examples:
      > SELECT _FUNC_(array('b', 'd', 'c', 'a'), true);
       ["a","b","c","d"]
  """)
// scalastyle:on line.size.limit
case class SortArray(base: Expression, ascendingOrder: Expression)
  extends BinaryExpression with ExpectsInputTypes with CodegenFallback {

  def this(e: Expression) = this(e, Literal(true))

  override def left: Expression = base
  override def right: Expression = ascendingOrder
  override def dataType: DataType = base.dataType
  override def inputTypes: Seq[AbstractDataType] = Seq(ArrayType, BooleanType)

  override def checkInputDataTypes(): TypeCheckResult = base.dataType match {
    case ArrayType(dt, _) if RowOrdering.isOrderable(dt) =>
      ascendingOrder match {
        case Literal(_: Boolean, BooleanType) =>
          TypeCheckResult.TypeCheckSuccess
        case _ =>
          TypeCheckResult.TypeCheckFailure(
            "Sort order in second argument requires a boolean literal.")
      }
    case ArrayType(dt, _) =>
      TypeCheckResult.TypeCheckFailure(
        s"$prettyName does not support sorting array of type ${dt.simpleString}")
    case _ =>
      TypeCheckResult.TypeCheckFailure(s"$prettyName only supports array input.")
  }

  @transient
  private lazy val lt: Comparator[Any] = {
    val ordering = base.dataType match {
      case _ @ ArrayType(n: AtomicType, _) => n.ordering.asInstanceOf[Ordering[Any]]
      case _ @ ArrayType(a: ArrayType, _) => a.interpretedOrdering.asInstanceOf[Ordering[Any]]
      case _ @ ArrayType(s: StructType, _) => s.interpretedOrdering.asInstanceOf[Ordering[Any]]
    }

    new Comparator[Any]() {
      override def compare(o1: Any, o2: Any): Int = {
        if (o1 == null && o2 == null) {
          0
        } else if (o1 == null) {
          -1
        } else if (o2 == null) {
          1
        } else {
          ordering.compare(o1, o2)
        }
      }
    }
  }

  @transient
  private lazy val gt: Comparator[Any] = {
    val ordering = base.dataType match {
      case _ @ ArrayType(n: AtomicType, _) => n.ordering.asInstanceOf[Ordering[Any]]
      case _ @ ArrayType(a: ArrayType, _) => a.interpretedOrdering.asInstanceOf[Ordering[Any]]
      case _ @ ArrayType(s: StructType, _) => s.interpretedOrdering.asInstanceOf[Ordering[Any]]
    }

    new Comparator[Any]() {
      override def compare(o1: Any, o2: Any): Int = {
        if (o1 == null && o2 == null) {
          0
        } else if (o1 == null) {
          1
        } else if (o2 == null) {
          -1
        } else {
          -ordering.compare(o1, o2)
        }
      }
    }
  }

  override def nullSafeEval(array: Any, ascending: Any): Any = {
    val elementType = base.dataType.asInstanceOf[ArrayType].elementType
    val data = array.asInstanceOf[ArrayData].toArray[AnyRef](elementType)
    if (elementType != NullType) {
      java.util.Arrays.sort(data, if (ascending.asInstanceOf[Boolean]) lt else gt)
    }
    new GenericArrayData(data.asInstanceOf[Array[Any]])
  }

  override def prettyName: String = "sort_array"
}

/**
 * Returns a reversed string or an array with reverse order of elements.
 */
@ExpressionDescription(
  usage = "_FUNC_(array) - Returns a reversed string or an array with reverse order of elements.",
  examples = """
    Examples:
      > SELECT _FUNC_('Spark SQL');
       LQS krapS
      > SELECT _FUNC_(array(2, 1, 4, 3));
       [3, 4, 1, 2]
  """,
  since = "1.5.0",
  note = "Reverse logic for arrays is available since 2.4.0."
)
case class Reverse(child: Expression) extends UnaryExpression with ImplicitCastInputTypes {

  // Input types are utilized by type coercion in ImplicitTypeCasts.
  override def inputTypes: Seq[AbstractDataType] = Seq(TypeCollection(StringType, ArrayType))

  override def dataType: DataType = child.dataType

  lazy val elementType: DataType = dataType.asInstanceOf[ArrayType].elementType

  override def nullSafeEval(input: Any): Any = input match {
    case a: ArrayData => new GenericArrayData(a.toObjectArray(elementType).reverse)
    case s: UTF8String => s.reverse()
  }

  override def doGenCode(ctx: CodegenContext, ev: ExprCode): ExprCode = {
    nullSafeCodeGen(ctx, ev, c => dataType match {
      case _: StringType => stringCodeGen(ev, c)
      case _: ArrayType => arrayCodeGen(ctx, ev, c)
    })
  }

  private def stringCodeGen(ev: ExprCode, childName: String): String = {
    s"${ev.value} = ($childName).reverse();"
  }

  private def arrayCodeGen(ctx: CodegenContext, ev: ExprCode, childName: String): String = {
    val length = ctx.freshName("length")
    val javaElementType = CodeGenerator.javaType(elementType)
    val isPrimitiveType = CodeGenerator.isPrimitiveType(elementType)

    val initialization = if (isPrimitiveType) {
      s"$childName.copy()"
    } else {
      s"new ${classOf[GenericArrayData].getName()}(new Object[$length])"
    }

    val numberOfIterations = if (isPrimitiveType) s"$length / 2" else length

    val swapAssigments = if (isPrimitiveType) {
      val setFunc = "set" + CodeGenerator.primitiveTypeName(elementType)
      val getCall = (index: String) => CodeGenerator.getValue(ev.value, elementType, index)
      s"""|boolean isNullAtK = ${ev.value}.isNullAt(k);
          |boolean isNullAtL = ${ev.value}.isNullAt(l);
          |if(!isNullAtK) {
          |  $javaElementType el = ${getCall("k")};
          |  if(!isNullAtL) {
          |    ${ev.value}.$setFunc(k, ${getCall("l")});
          |  } else {
          |    ${ev.value}.setNullAt(k);
          |  }
          |  ${ev.value}.$setFunc(l, el);
          |} else if (!isNullAtL) {
          |  ${ev.value}.$setFunc(k, ${getCall("l")});
          |  ${ev.value}.setNullAt(l);
          |}""".stripMargin
    } else {
      s"${ev.value}.update(k, ${CodeGenerator.getValue(childName, elementType, "l")});"
    }

    s"""
       |final int $length = $childName.numElements();
       |${ev.value} = $initialization;
       |for(int k = 0; k < $numberOfIterations; k++) {
       |  int l = $length - k - 1;
       |  $swapAssigments
       |}
     """.stripMargin
  }

  override def prettyName: String = "reverse"
}

/**
 * Checks if the array (left) has the element (right)
 */
@ExpressionDescription(
  usage = "_FUNC_(array, value) - Returns true if the array contains the value.",
  examples = """
    Examples:
      > SELECT _FUNC_(array(1, 2, 3), 2);
       true
  """)
case class ArrayContains(left: Expression, right: Expression)
  extends BinaryExpression with ImplicitCastInputTypes {

  override def dataType: DataType = BooleanType

  override def inputTypes: Seq[AbstractDataType] = right.dataType match {
    case NullType => Seq.empty
    case _ => left.dataType match {
      case n @ ArrayType(element, _) => Seq(n, element)
      case _ => Seq.empty
    }
  }

  override def checkInputDataTypes(): TypeCheckResult = {
    if (right.dataType == NullType) {
      TypeCheckResult.TypeCheckFailure("Null typed values cannot be used as arguments")
    } else if (!left.dataType.isInstanceOf[ArrayType]
      || left.dataType.asInstanceOf[ArrayType].elementType != right.dataType) {
      TypeCheckResult.TypeCheckFailure(
        "Arguments must be an array followed by a value of same type as the array members")
    } else {
      TypeCheckResult.TypeCheckSuccess
    }
  }

  override def nullable: Boolean = {
    left.nullable || right.nullable || left.dataType.asInstanceOf[ArrayType].containsNull
  }

  override def nullSafeEval(arr: Any, value: Any): Any = {
    var hasNull = false
    arr.asInstanceOf[ArrayData].foreach(right.dataType, (i, v) =>
      if (v == null) {
        hasNull = true
      } else if (v == value) {
        return true
      }
    )
    if (hasNull) {
      null
    } else {
      false
    }
  }

  override def doGenCode(ctx: CodegenContext, ev: ExprCode): ExprCode = {
    nullSafeCodeGen(ctx, ev, (arr, value) => {
      val i = ctx.freshName("i")
      val getValue = CodeGenerator.getValue(arr, right.dataType, i)
      s"""
      for (int $i = 0; $i < $arr.numElements(); $i ++) {
        if ($arr.isNullAt($i)) {
          ${ev.isNull} = true;
        } else if (${ctx.genEqual(right.dataType, value, getValue)}) {
          ${ev.isNull} = false;
          ${ev.value} = true;
          break;
        }
      }
     """
    })
  }

  override def prettyName: String = "array_contains"
}

/**
 * Returns the minimum value in the array.
 */
@ExpressionDescription(
  usage = "_FUNC_(array) - Returns the minimum value in the array. NULL elements are skipped.",
  examples = """
    Examples:
      > SELECT _FUNC_(array(1, 20, null, 3));
       1
  """, since = "2.4.0")
case class ArrayMin(child: Expression) extends UnaryExpression with ImplicitCastInputTypes {

  override def nullable: Boolean = true

  override def inputTypes: Seq[AbstractDataType] = Seq(ArrayType)

  private lazy val ordering = TypeUtils.getInterpretedOrdering(dataType)

  override def checkInputDataTypes(): TypeCheckResult = {
    val typeCheckResult = super.checkInputDataTypes()
    if (typeCheckResult.isSuccess) {
      TypeUtils.checkForOrderingExpr(dataType, s"function $prettyName")
    } else {
      typeCheckResult
    }
  }

  override protected def doGenCode(ctx: CodegenContext, ev: ExprCode): ExprCode = {
    val childGen = child.genCode(ctx)
    val javaType = CodeGenerator.javaType(dataType)
    val i = ctx.freshName("i")
    val item = ExprCode("",
      isNull = JavaCode.isNullExpression(s"${childGen.value}.isNullAt($i)"),
      value = JavaCode.expression(CodeGenerator.getValue(childGen.value, dataType, i), dataType))
    ev.copy(code =
      s"""
         |${childGen.code}
         |boolean ${ev.isNull} = true;
         |$javaType ${ev.value} = ${CodeGenerator.defaultValue(dataType)};
         |if (!${childGen.isNull}) {
         |  for (int $i = 0; $i < ${childGen.value}.numElements(); $i ++) {
         |    ${ctx.reassignIfSmaller(dataType, ev, item)}
         |  }
         |}
      """.stripMargin)
  }

  override protected def nullSafeEval(input: Any): Any = {
    var min: Any = null
    input.asInstanceOf[ArrayData].foreach(dataType, (_, item) =>
      if (item != null && (min == null || ordering.lt(item, min))) {
        min = item
      }
    )
    min
  }

  override def dataType: DataType = child.dataType match {
    case ArrayType(dt, _) => dt
    case _ => throw new IllegalStateException(s"$prettyName accepts only arrays.")
  }

  override def prettyName: String = "array_min"
}

/**
 * Returns the maximum value in the array.
 */
@ExpressionDescription(
  usage = "_FUNC_(array) - Returns the maximum value in the array. NULL elements are skipped.",
  examples = """
    Examples:
      > SELECT _FUNC_(array(1, 20, null, 3));
       20
  """, since = "2.4.0")
case class ArrayMax(child: Expression) extends UnaryExpression with ImplicitCastInputTypes {

  override def nullable: Boolean = true

  override def inputTypes: Seq[AbstractDataType] = Seq(ArrayType)

  private lazy val ordering = TypeUtils.getInterpretedOrdering(dataType)

  override def checkInputDataTypes(): TypeCheckResult = {
    val typeCheckResult = super.checkInputDataTypes()
    if (typeCheckResult.isSuccess) {
      TypeUtils.checkForOrderingExpr(dataType, s"function $prettyName")
    } else {
      typeCheckResult
    }
  }

  override protected def doGenCode(ctx: CodegenContext, ev: ExprCode): ExprCode = {
    val childGen = child.genCode(ctx)
    val javaType = CodeGenerator.javaType(dataType)
    val i = ctx.freshName("i")
    val item = ExprCode("",
      isNull = JavaCode.isNullExpression(s"${childGen.value}.isNullAt($i)"),
      value = JavaCode.expression(CodeGenerator.getValue(childGen.value, dataType, i), dataType))
    ev.copy(code =
      s"""
         |${childGen.code}
         |boolean ${ev.isNull} = true;
         |$javaType ${ev.value} = ${CodeGenerator.defaultValue(dataType)};
         |if (!${childGen.isNull}) {
         |  for (int $i = 0; $i < ${childGen.value}.numElements(); $i ++) {
         |    ${ctx.reassignIfGreater(dataType, ev, item)}
         |  }
         |}
      """.stripMargin)
  }

  override protected def nullSafeEval(input: Any): Any = {
    var max: Any = null
    input.asInstanceOf[ArrayData].foreach(dataType, (_, item) =>
      if (item != null && (max == null || ordering.gt(item, max))) {
        max = item
      }
    )
    max
  }

  override def dataType: DataType = child.dataType match {
    case ArrayType(dt, _) => dt
    case _ => throw new IllegalStateException(s"$prettyName accepts only arrays.")
  }

  override def prettyName: String = "array_max"
}


/**
 * Returns the position of the first occurrence of element in the given array as long.
 * Returns 0 if the given value could not be found in the array. Returns null if either of
 * the arguments are null
 *
 * NOTE: that this is not zero based, but 1-based index. The first element in the array has
 *       index 1.
 */
@ExpressionDescription(
  usage = """
    _FUNC_(array, element) - Returns the (1-based) index of the first element of the array as long.
  """,
  examples = """
    Examples:
      > SELECT _FUNC_(array(3, 2, 1), 1);
       3
  """,
  since = "2.4.0")
case class ArrayPosition(left: Expression, right: Expression)
  extends BinaryExpression with ImplicitCastInputTypes {

  override def dataType: DataType = LongType
  override def inputTypes: Seq[AbstractDataType] =
    Seq(ArrayType, left.dataType.asInstanceOf[ArrayType].elementType)

  override def nullSafeEval(arr: Any, value: Any): Any = {
    arr.asInstanceOf[ArrayData].foreach(right.dataType, (i, v) =>
      if (v == value) {
        return (i + 1).toLong
      }
    )
    0L
  }

  override def prettyName: String = "array_position"

  override def doGenCode(ctx: CodegenContext, ev: ExprCode): ExprCode = {
    nullSafeCodeGen(ctx, ev, (arr, value) => {
      val pos = ctx.freshName("arrayPosition")
      val i = ctx.freshName("i")
      val getValue = CodeGenerator.getValue(arr, right.dataType, i)
      s"""
         |int $pos = 0;
         |for (int $i = 0; $i < $arr.numElements(); $i ++) {
         |  if (!$arr.isNullAt($i) && ${ctx.genEqual(right.dataType, value, getValue)}) {
         |    $pos = $i + 1;
         |    break;
         |  }
         |}
         |${ev.value} = (long) $pos;
       """.stripMargin
    })
  }
}

/**
 * Returns the value of index `right` in Array `left` or the value for key `right` in Map `left`.
 */
@ExpressionDescription(
  usage = """
    _FUNC_(array, index) - Returns element of array at given (1-based) index. If index < 0,
      accesses elements from the last to the first. Returns NULL if the index exceeds the length
      of the array.

    _FUNC_(map, key) - Returns value for given key, or NULL if the key is not contained in the map
  """,
  examples = """
    Examples:
      > SELECT _FUNC_(array(1, 2, 3), 2);
       2
      > SELECT _FUNC_(map(1, 'a', 2, 'b'), 2);
       "b"
  """,
  since = "2.4.0")
case class ElementAt(left: Expression, right: Expression) extends GetMapValueUtil {

  override def dataType: DataType = left.dataType match {
    case ArrayType(elementType, _) => elementType
    case MapType(_, valueType, _) => valueType
  }

  override def inputTypes: Seq[AbstractDataType] = {
    Seq(TypeCollection(ArrayType, MapType),
      left.dataType match {
        case _: ArrayType => IntegerType
        case _: MapType => left.dataType.asInstanceOf[MapType].keyType
      }
    )
  }

  override def nullable: Boolean = true

  override def nullSafeEval(value: Any, ordinal: Any): Any = {
    left.dataType match {
      case _: ArrayType =>
        val array = value.asInstanceOf[ArrayData]
        val index = ordinal.asInstanceOf[Int]
        if (array.numElements() < math.abs(index)) {
          null
        } else {
          val idx = if (index == 0) {
            throw new ArrayIndexOutOfBoundsException("SQL array indices start at 1")
          } else if (index > 0) {
            index - 1
          } else {
            array.numElements() + index
          }
          if (left.dataType.asInstanceOf[ArrayType].containsNull && array.isNullAt(idx)) {
            null
          } else {
            array.get(idx, dataType)
          }
        }
      case _: MapType =>
        getValueEval(value, ordinal, left.dataType.asInstanceOf[MapType].keyType)
    }
  }

  override def doGenCode(ctx: CodegenContext, ev: ExprCode): ExprCode = {
    left.dataType match {
      case _: ArrayType =>
        nullSafeCodeGen(ctx, ev, (eval1, eval2) => {
          val index = ctx.freshName("elementAtIndex")
          val nullCheck = if (left.dataType.asInstanceOf[ArrayType].containsNull) {
            s"""
               |if ($eval1.isNullAt($index)) {
               |  ${ev.isNull} = true;
               |} else
             """.stripMargin
          } else {
            ""
          }
          s"""
             |int $index = (int) $eval2;
             |if ($eval1.numElements() < Math.abs($index)) {
             |  ${ev.isNull} = true;
             |} else {
             |  if ($index == 0) {
             |    throw new ArrayIndexOutOfBoundsException("SQL array indices start at 1");
             |  } else if ($index > 0) {
             |    $index--;
             |  } else {
             |    $index += $eval1.numElements();
             |  }
             |  $nullCheck
             |  {
             |    ${ev.value} = ${CodeGenerator.getValue(eval1, dataType, index)};
             |  }
             |}
           """.stripMargin
        })
      case _: MapType =>
        doGetValueGenCode(ctx, ev, left.dataType.asInstanceOf[MapType])
    }
  }

  override def prettyName: String = "element_at"
}

/**
 * Concatenates multiple input columns together into a single column.
 * The function works with strings, binary and compatible array columns.
 */
@ExpressionDescription(
  usage = "_FUNC_(col1, col2, ..., colN) - Returns the concatenation of col1, col2, ..., colN.",
  examples = """
    Examples:
      > SELECT _FUNC_('Spark', 'SQL');
       SparkSQL
      > SELECT _FUNC_(array(1, 2, 3), array(4, 5), array(6));
 |     [1,2,3,4,5,6]
  """)
case class Concat(children: Seq[Expression]) extends Expression {

  private val MAX_ARRAY_LENGTH: Int = ByteArrayMethods.MAX_ROUNDED_ARRAY_LENGTH

  val allowedTypes = Seq(StringType, BinaryType, ArrayType)

  override def checkInputDataTypes(): TypeCheckResult = {
    if (children.isEmpty) {
      TypeCheckResult.TypeCheckSuccess
    } else {
      val childTypes = children.map(_.dataType)
      if (childTypes.exists(tpe => !allowedTypes.exists(_.acceptsType(tpe)))) {
        return TypeCheckResult.TypeCheckFailure(
          s"input to function $prettyName should have been StringType, BinaryType or ArrayType," +
            s" but it's " + childTypes.map(_.simpleString).mkString("[", ", ", "]"))
      }
      TypeUtils.checkForSameTypeInputExpr(childTypes, s"function $prettyName")
    }
  }

  override def dataType: DataType = children.map(_.dataType).headOption.getOrElse(StringType)

  lazy val javaType: String = CodeGenerator.javaType(dataType)

  override def nullable: Boolean = children.exists(_.nullable)

  override def foldable: Boolean = children.forall(_.foldable)

  override def eval(input: InternalRow): Any = dataType match {
    case BinaryType =>
      val inputs = children.map(_.eval(input).asInstanceOf[Array[Byte]])
      ByteArray.concat(inputs: _*)
    case StringType =>
      val inputs = children.map(_.eval(input).asInstanceOf[UTF8String])
      UTF8String.concat(inputs : _*)
    case ArrayType(elementType, _) =>
      val inputs = children.toStream.map(_.eval(input))
      if (inputs.contains(null)) {
        null
      } else {
        val arrayData = inputs.map(_.asInstanceOf[ArrayData])
        val numberOfElements = arrayData.foldLeft(0L)((sum, ad) => sum + ad.numElements())
        if (numberOfElements > MAX_ARRAY_LENGTH) {
          throw new RuntimeException(s"Unsuccessful try to concat arrays with $numberOfElements" +
            s" elements due to exceeding the array size limit $MAX_ARRAY_LENGTH.")
        }
        val finalData = new Array[AnyRef](numberOfElements.toInt)
        var position = 0
        for(ad <- arrayData) {
          val arr = ad.toObjectArray(elementType)
          Array.copy(arr, 0, finalData, position, arr.length)
          position += arr.length
        }
        new GenericArrayData(finalData)
      }
  }

  override protected def doGenCode(ctx: CodegenContext, ev: ExprCode): ExprCode = {
    val evals = children.map(_.genCode(ctx))
    val args = ctx.freshName("args")

    val inputs = evals.zipWithIndex.map { case (eval, index) =>
      s"""
        ${eval.code}
        if (!${eval.isNull}) {
          $args[$index] = ${eval.value};
        }
      """
    }

    val (concatenator, initCode) = dataType match {
      case BinaryType =>
        (classOf[ByteArray].getName, s"byte[][] $args = new byte[${evals.length}][];")
      case StringType =>
        ("UTF8String", s"UTF8String[] $args = new UTF8String[${evals.length}];")
      case ArrayType(elementType, _) =>
        val arrayConcatClass = if (CodeGenerator.isPrimitiveType(elementType)) {
          genCodeForPrimitiveArrays(ctx, elementType)
        } else {
          genCodeForNonPrimitiveArrays(ctx, elementType)
        }
        (arrayConcatClass, s"ArrayData[] $args = new ArrayData[${evals.length}];")
    }
    val codes = ctx.splitExpressionsWithCurrentInputs(
      expressions = inputs,
      funcName = "valueConcat",
      extraArguments = (s"$javaType[]", args) :: Nil)
    ev.copy(s"""
      $initCode
      $codes
      $javaType ${ev.value} = $concatenator.concat($args);
      boolean ${ev.isNull} = ${ev.value} == null;
    """)
  }

  private def genCodeForNumberOfElements(ctx: CodegenContext) : (String, String) = {
    val numElements = ctx.freshName("numElements")
    val code = s"""
        |long $numElements = 0L;
        |for (int z = 0; z < ${children.length}; z++) {
        |  $numElements += args[z].numElements();
        |}
        |if ($numElements > $MAX_ARRAY_LENGTH) {
        |  throw new RuntimeException("Unsuccessful try to concat arrays with " + $numElements +
        |    " elements due to exceeding the array size limit $MAX_ARRAY_LENGTH.");
        |}
      """.stripMargin

    (code, numElements)
  }

  private def nullArgumentProtection() : String = {
    if (nullable) {
      s"""
         |for (int z = 0; z < ${children.length}; z++) {
         |  if (args[z] == null) return null;
         |}
       """.stripMargin
    } else {
      ""
    }
  }

  private def genCodeForPrimitiveArrays(ctx: CodegenContext, elementType: DataType): String = {
    val arrayName = ctx.freshName("array")
    val arraySizeName = ctx.freshName("size")
    val counter = ctx.freshName("counter")
    val arrayData = ctx.freshName("arrayData")

    val (numElemCode, numElemName) = genCodeForNumberOfElements(ctx)

    val unsafeArraySizeInBytes = s"""
      |long $arraySizeName = UnsafeArrayData.calculateSizeOfUnderlyingByteArray(
      |  $numElemName,
      |  ${elementType.defaultSize});
      |if ($arraySizeName > $MAX_ARRAY_LENGTH) {
      |  throw new RuntimeException("Unsuccessful try to concat arrays with " + $arraySizeName +
      |    " bytes of data due to exceeding the limit $MAX_ARRAY_LENGTH bytes" +
      |    " for UnsafeArrayData.");
      |}
      """.stripMargin
    val baseOffset = Platform.BYTE_ARRAY_OFFSET
    val primitiveValueTypeName = CodeGenerator.primitiveTypeName(elementType)

    s"""
       |new Object() {
       |  public ArrayData concat($javaType[] args) {
       |    ${nullArgumentProtection()}
       |    $numElemCode
       |    $unsafeArraySizeInBytes
       |    byte[] $arrayName = new byte[(int)$arraySizeName];
       |    UnsafeArrayData $arrayData = new UnsafeArrayData();
       |    Platform.putLong($arrayName, $baseOffset, $numElemName);
       |    $arrayData.pointTo($arrayName, $baseOffset, (int)$arraySizeName);
       |    int $counter = 0;
       |    for (int y = 0; y < ${children.length}; y++) {
       |      for (int z = 0; z < args[y].numElements(); z++) {
       |        if (args[y].isNullAt(z)) {
       |          $arrayData.setNullAt($counter);
       |        } else {
       |          $arrayData.set$primitiveValueTypeName(
       |            $counter,
       |            ${CodeGenerator.getValue(s"args[y]", elementType, "z")}
       |          );
       |        }
       |        $counter++;
       |      }
       |    }
       |    return $arrayData;
       |  }
       |}""".stripMargin.stripPrefix("\n")
  }

  private def genCodeForNonPrimitiveArrays(ctx: CodegenContext, elementType: DataType): String = {
    val genericArrayClass = classOf[GenericArrayData].getName
    val arrayData = ctx.freshName("arrayObjects")
    val counter = ctx.freshName("counter")

    val (numElemCode, numElemName) = genCodeForNumberOfElements(ctx)

    s"""
       |new Object() {
       |  public ArrayData concat($javaType[] args) {
       |    ${nullArgumentProtection()}
       |    $numElemCode
       |    Object[] $arrayData = new Object[(int)$numElemName];
       |    int $counter = 0;
       |    for (int y = 0; y < ${children.length}; y++) {
       |      for (int z = 0; z < args[y].numElements(); z++) {
       |        $arrayData[$counter] = ${CodeGenerator.getValue(s"args[y]", elementType, "z")};
       |        $counter++;
       |      }
       |    }
       |    return new $genericArrayClass($arrayData);
       |  }
       |}""".stripMargin.stripPrefix("\n")
  }

  override def toString: String = s"concat(${children.mkString(", ")})"

  override def sql: String = s"concat(${children.map(_.sql).mkString(", ")})"
}

object ArraySetUtils {
  val kindUnion = 1
  val kindIntersection = 2
  val kindExcept = 3

  def toUnsafeIntArray(hs: OpenHashSet[Int]): UnsafeArrayData = {
    val array = new Array[Int](hs.size)
    var pos = hs.nextPos(0)
    var i = 0
    while (pos != OpenHashSet.INVALID_POS) {
      array(i) = hs.getValue(pos)
      pos = hs.nextPos(pos + 1)
      i += 1
    }
    UnsafeArrayData.fromPrimitiveArray(array)
  }

  def toUnsafeLongArray(hs: OpenHashSet[Long]): UnsafeArrayData = {
    val array = new Array[Long](hs.size)
    var pos = hs.nextPos(0)
    var i = 0
    while (pos != OpenHashSet.INVALID_POS) {
      array(i) = hs.getValue(pos)
      pos = hs.nextPos(pos + 1)
      i += 1
    }
    UnsafeArrayData.fromPrimitiveArray(array)
  }

  def arrayUnion(array1: ArrayData, array2: ArrayData, et: DataType): ArrayData = {
    new GenericArrayData(array1.toArray[AnyRef](et).union(array2.toArray[AnyRef](et))
      .distinct.asInstanceOf[Array[Any]])
  }

  def arrayIntersect(array1: ArrayData, array2: ArrayData, et: DataType): ArrayData = {
    new GenericArrayData(array1.toArray[AnyRef](et).intersect(array2.toArray[AnyRef](et))
      .distinct.asInstanceOf[Array[Any]])
  }

  def arrayExcept(array1: ArrayData, array2: ArrayData, et: DataType): ArrayData = {
    new GenericArrayData(array1.toArray[AnyRef](et).diff(array2.toArray[AnyRef](et))
      .distinct.asInstanceOf[Array[Any]])
  }
}

abstract class ArraySetUtils extends BinaryExpression with ExpectsInputTypes {
  def typeId: Int

  override def inputTypes: Seq[AbstractDataType] = Seq(ArrayType, ArrayType)

  override def checkInputDataTypes(): TypeCheckResult = {
    val r = super.checkInputDataTypes()
    if ((r == TypeCheckResult.TypeCheckSuccess) &&
      (left.dataType.asInstanceOf[ArrayType].elementType !=
        right.dataType.asInstanceOf[ArrayType].elementType)) {
      TypeCheckResult.TypeCheckFailure("Element type in both arrays must be the same")
    } else {
      r
    }
  }

  override def dataType: DataType = left.dataType

  private def elementType = dataType.asInstanceOf[ArrayType].elementType
  private def cn = left.dataType.asInstanceOf[ArrayType].containsNull ||
    right.dataType.asInstanceOf[ArrayType].containsNull

  def intEval(ary: ArrayData, hs2: OpenHashSet[Int]): OpenHashSet[Int]
  def longEval(ary: ArrayData, hs2: OpenHashSet[Long]): OpenHashSet[Long]
  def genericEval(ary: ArrayData, hs2: OpenHashSet[Any], et: DataType): OpenHashSet[Any]
  def codeGen(ctx: CodegenContext, classTag : String, hs2: String, hs: String, len: String,
              getter: String, i: String,
              postFix: String, newOpenHashSet: String): String

  override def nullSafeEval(input1: Any, input2: Any): Any = {
    val ary1 = input1.asInstanceOf[ArrayData]
    val ary2 = input2.asInstanceOf[ArrayData]

    if (!cn) {
      elementType match {
        case IntegerType =>
          // avoid boxing of primitive int array elements
          val hs2 = new OpenHashSet[Int]
          var i = 0
          while (i < ary2.numElements()) {
            hs2.add(ary2.getInt(i))
            i += 1
          }
          ArraySetUtils.toUnsafeIntArray(intEval(ary1, hs2))
        case LongType =>
          // avoid boxing of primitive long array elements
          val hs2 = new OpenHashSet[Long]
          var i = 0
          while (i < ary2.numElements()) {
            hs2.add(ary2.getLong(i))
            i += 1
          }
          ArraySetUtils.toUnsafeLongArray(longEval(ary1, hs2))
        case _ =>
          val hs2 = new OpenHashSet[Any]
          var i = 0
          while (i < ary2.numElements()) {
            hs2.add(ary2.get(i, elementType))
            i += 1
          }
          new GenericArrayData(genericEval(ary1, hs2, elementType).iterator.toArray)
      }
    } else {
      if (typeId == ArraySetUtils.kindUnion) {
        ArraySetUtils.arrayUnion(ary1, ary2, elementType)
      } else if (typeId == ArraySetUtils.kindIntersection) {
        ArraySetUtils.arrayIntersect(ary1, ary2, elementType)
      } else if (typeId == ArraySetUtils.kindExcept) {
        ArraySetUtils.arrayExcept(ary1, ary2, elementType)
      } else {
        null
      }
    }
  }

  override def doGenCode(ctx: CodegenContext, ev: ExprCode): ExprCode = {
    val i = ctx.freshName("i")
    val arraySetUtils = "org.apache.spark.sql.catalyst.expressions.ArraySetUtils"
    val genericArrayData = classOf[GenericArrayData].getName
    val unsafeArrayData = classOf[UnsafeArrayData].getName
    val openHashSet = classOf[OpenHashSet[_]].getName
    val et = s"org.apache.spark.sql.types.DataTypes.$elementType"
    val (postFix, classTag, getter, arrayBuilder, javaTypeName) = if (!cn) {
      val ptName = CodeGenerator.primitiveTypeName(elementType)
      elementType match {
        case ByteType | ShortType | IntegerType =>
          (s"$$mcI$$sp", s"scala.reflect.ClassTag$$.MODULE$$.$ptName()", s"get$ptName($i)",
            s"$unsafeArrayData.fromPrimitiveArray", CodeGenerator.javaType(elementType))
        case LongType =>
          (s"$$mcJ$$sp", s"scala.reflect.ClassTag$$.MODULE$$.$ptName()", s"get$ptName($i)",
            s"$unsafeArrayData.fromPrimitiveArray", "long")
        case _ =>
          ("", s"scala.reflect.ClassTag$$.MODULE$$.Object()", s"get($i, $et)",
            s"new $genericArrayData", "Object")
      }
    } else {
      ("", "", "", "", "")
    }

    val hs = ctx.freshName("hs")
    val hs2 = ctx.freshName("hs2")
    val invalidPos = ctx.freshName("invalidPos")
    val pos = ctx.freshName("pos")
    val ary = ctx.freshName("ary")
    nullSafeCodeGen(ctx, ev, (ary1, ary2) => {
      if (classTag != "") {
        val secondLoop = codeGen(ctx, classTag, hs2, hs, s"$ary1.numElements()",
          s"$ary1.$getter", i,
          postFix, s"new $openHashSet$postFix($classTag)")
        s"""
           |$openHashSet $hs2 = new $openHashSet$postFix($classTag);
           |for (int $i = 0; $i < $ary2.numElements(); $i++) {
           |  $hs2.add$postFix($ary2.$getter);
           |}
           |$secondLoop
           |$javaTypeName[] $ary = new $javaTypeName[$hs.size()];
           |int $invalidPos = $openHashSet.INVALID_POS();
           |int $pos = $hs.nextPos(0);
           |int $i = 0;
           |while ($pos != $invalidPos) {
           |  $ary[$i] = ($javaTypeName) $hs.getValue$postFix($pos);
           |  $pos = $hs.nextPos($pos + 1);
           |  $i++;
           |}
           |${ev.value} = $arrayBuilder($ary);
         """.stripMargin
      } else {
        val setOp = if (typeId == ArraySetUtils.kindUnion) {
          "Union"
        } else if (typeId == ArraySetUtils.kindIntersection) {
          "Intersect"
        } else if (typeId == ArraySetUtils.kindExcept) {
          "Except"
        } else {
          ""
        }
        s"${ev.value} = $arraySetUtils$$.MODULE$$.array$setOp($ary1, $ary2, $et);"
      }
    })
  }
}


@ExpressionDescription(
  usage = """
    _FUNC_(array1, array2) - Returns an array of the elements in the union of array1 and array2,
      without duplicates. The order of elements in the result is not determined.
  """,
  examples = """
    Examples:
      > SELECT _FUNC_(array(1, 2, 3), array(1, 3, 5));
       array(1, 2, 3, 5)
  """,
  since = "2.4.0")
case class ArrayUnion(left: Expression, right: Expression) extends ArraySetUtils {
  override def typeId: Int = ArraySetUtils.kindUnion

  override def intEval(ary: ArrayData, hs2: OpenHashSet[Int]): OpenHashSet[Int] = {
    var i = 0
    while (i < ary.numElements()) {
      hs2.add(ary.getInt(i))
      i += 1
    }
    hs2
  }

  override def longEval(ary: ArrayData, hs2: OpenHashSet[Long]): OpenHashSet[Long] = {
    var i = 0
    while (i < ary.numElements()) {
      hs2.add(ary.getLong(i))
      i += 1
    }
    hs2
  }

  override def genericEval(
                            ary: ArrayData,
                            hs2: OpenHashSet[Any],
                            et: DataType): OpenHashSet[Any] = {
    var i = 0
    while (i < ary.numElements()) {
      hs2.add(ary.get(i, et))
      i += 1
    }
    hs2
  }

  override def codeGen(
                        ctx: CodegenContext,
                        classTag: String,
                        hs2: String,
                        hs: String,
                        len: String,
                        getter: String,
                        i: String,
                        postFix: String,
                        newOpenHashSet: String): String = {
    val openHashSet = classOf[OpenHashSet[_]].getName
    s"""
       |for (int $i = 0; $i < $len; $i++) {
       |  $hs2.add$postFix($getter);
       |}
       |$openHashSet $hs = $hs2;
     """.stripMargin
  }

  override def prettyName: String = "array_union"
}

@ExpressionDescription(
  usage = """
    _FUNC_(array1, array2) - Returns an array of the elements in the intersection of array1 and array2,
      without duplicates. The order of elements in the result is not determined.
  """,
  examples = """
    Examples:
      > SELECT _FUNC_(array(1, 2, 3), array(1, 3, 5));
       array(1, 3)
  """
  )
case class ArrayIntersection(left: Expression, right: Expression) extends ArraySetUtils {
  override def typeId: Int = ArraySetUtils.kindIntersection

  override def intEval(ary: ArrayData, hs2: OpenHashSet[Int]): OpenHashSet[Int] = {
    var i = 0
    val hs1 = new OpenHashSet[Int]
    while (i < ary.numElements()) {
      val current = ary.getInt(i)
      if (hs2.contains(current)) {
        hs1.add(current)
      }
      i += 1
    }
    hs1
  }

  override def longEval(ary: ArrayData, hs2: OpenHashSet[Long]): OpenHashSet[Long] = {
    var i = 0
    val hs1 = new OpenHashSet[Long]
    while (i < ary.numElements()) {
      val current = ary.getLong(i)
      if (hs2.contains(current)) {
        hs1.add(current)
      }
      i += 1
    }
    hs1
  }

  override def genericEval(
                            ary: ArrayData,
                            hs2: OpenHashSet[Any],
                            et: DataType): OpenHashSet[Any] = {
    var i = 0
    val hs1 = new OpenHashSet[Any]
    while (i < ary.numElements()) {
      val current = ary.get(i, et)
      if (hs2.contains(current)) {
        hs1.add(current)
      }
      i += 1
    }
    hs1
  }

  override def codeGen(
                        ctx: CodegenContext,
                        classTag: String,
                        hs2: String,
                        hs: String,
                        len: String,
                        getter: String,
                        i: String,
                        postFix: String,
                        newOpenHashSet: String): String = {
    val openHashSet = classOf[OpenHashSet[_]].getName
    s"""
       |$openHashSet $hs = new $openHashSet$postFix($classTag);
       |for (int $i = 0; $i < $len; $i++) {
       |  if ($hs2.contains($getter)) {
       |     $hs.add$postFix($getter);
       |  }
       |}
     """.stripMargin
  }

  override def prettyName: String = "array_intersection"
}


@ExpressionDescription(
  usage = """
    _FUNC_(array1, array2) - Returns an array of the elements that are in array1 but not in array2,
      without duplicates. The order of elements in the result is not determined.
  """,
  examples = """
    Examples:
      > SELECT _FUNC_(array(1, 2, 3), array(1, 3, 5));
       array(1, 3)
  """
)
case class ArrayExcept(left: Expression, right: Expression) extends ArraySetUtils {
  override def typeId: Int = ArraySetUtils.kindExcept

  override def intEval(ary: ArrayData, hs2: OpenHashSet[Int]): OpenHashSet[Int] = {
    var i = 0
    val hs1 = new OpenHashSet[Int]
    while (i < ary.numElements()) {
      val current = ary.getInt(i)
      if (!hs2.contains(current)) {
        hs1.add(current)
      }
      i += 1
    }
    hs1
  }

  override def longEval(ary: ArrayData, hs2: OpenHashSet[Long]): OpenHashSet[Long] = {
    var i = 0
    val hs1 = new OpenHashSet[Long]
    while (i < ary.numElements()) {
      val current = ary.getLong(i)
      if (!hs2.contains(current)) {
        hs1.add(current)
      }
      i += 1
    }
    hs1
  }

  override def genericEval(
                            ary: ArrayData,
                            hs2: OpenHashSet[Any],
                            et: DataType): OpenHashSet[Any] = {
    var i = 0
    val hs1 = new OpenHashSet[Any]
    while (i < ary.numElements()) {
      val current = ary.get(i, et)
      if (!hs2.contains(current)) {
        hs1.add(current)
      }
      i += 1
    }
    hs1
  }

  override def codeGen(
                        ctx: CodegenContext,
                        classTag: String,
                        hs2: String,
                        hs: String,
                        len: String,
                        getter: String,
                        i: String,
                        postFix: String,
                        newOpenHashSet: String): String = {
    val openHashSet = classOf[OpenHashSet[_]].getName
    s"""
       |$openHashSet $hs = new $openHashSet$postFix($classTag);
       |for (int $i = 0; $i < $len; $i++) {
       |  if (!$hs2.contains($getter)) {
       |     $hs.add$postFix($getter);
       |  }
       |}
     """.stripMargin
  }

  override def prettyName: String = "array_except"
}
