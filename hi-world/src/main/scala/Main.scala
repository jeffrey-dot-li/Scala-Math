import math._
import scala.language.implicitConversions
import scala.collection._
import algebra.ring._
import shapeless.Nats
// import Somebody
object Test {
  import shapeless._
  import nat._
  import newtype._
  import ops.hlist.{Mapper, Transposer}
  import ops.product.ProductLength
  import test._
  import ops.nat._
  import algebra.ring._
  import cats._
  import shapeless.syntax.sized._

  def zip[A, B, N <: Nat](l: Sized[Seq[A], N], r: Sized[Seq[B], N])
    (implicit cbf: BuildFrom[Seq[A], (A, B), Seq[(A, B)]], ev: AdditiveCollection[Seq[(A, B)]])
    : Sized[Seq[(A, B)], N] =
    Sized.wrap[Seq[(A, B)], N](l.unsized zip r.unsized)

  // val nat: Nat = 3;
  // Type N = 3;
  // val sizedBoi : Sized[Seq[Int], N] = Sized(1,2,3)

  // Define like n-vector, and n-vector transpose.
  // Define product which sends v * v^t => 1x1
  


  val doubleScalarField = new Field[Double] {
    def div(x: Double, y: Double): Double = x / y
    def negate(x: Double): Double = -x
    def one: Double = 1
    def plus(x: Double, y: Double): Double = x + y
    def times(x: Double, y: Double): Double = x * y
    def zero: Double = 0

  }

  // class Monoid[]

  class PolynomialRing[VF <: VectorField[N, ScalarType], N <: Nat, ScalarType]
    (val vectorField: VF) {
    def scalarField = vectorField.scalarField
    type NVectorType = vectorField.NVectorType
    type PolyType = Vector[(ScalarType, NVectorType)]
    type NPolyType = Newtype[PolyType, PolyOps]

    def polynomialRing = new Ring[NPolyType] {
      def negate(x: NPolyType) = -x
      def plus(x: NPolyType, y: NPolyType) = x + y
      def times(x: NPolyType, y: NPolyType) = x * y
      def zero = apply(Vector.empty[(ScalarType, NVectorType)])
      def one = apply(Vector((scalarField.one, vectorField.AdditiveGroup.empty)))
    }

    abstract class PolyOps(p: PolyType) {
      type Self = Newtype[PolyType, PolyOps];
      def poly = p
      override def toString = poly.toString
      def +(other: Self): Self;
      def unary_- : Self;
      def *(other: Self): Self;
    }

    object PolyOps {
      implicit def pointOps(p: PolyType): PolyOps = new PolyOps(p) {
        def +(other: Self) = newtype(
          poly ++ other.poly
        );
        def *(other: Self): Self = newtype(
          poly.foldLeft(polynomialRing.zero.poly)((prev, cx) =>
            other.poly.map(cy => (scalarField.times(cy._1, cx._1), cx._2 + cy._2))
          )
        )
        def unary_- : Self = newtype(p.map(t => (scalarField.negate(t._1), t._2)))
      }
    }
    def apply(v: PolyType) =
      newtype[PolyType, PolyOps](v)
  }

  class MonoidExtension[+MonoidField <: Monoid[ElementType], N <: Nat, ElementType]
    (val monoid: MonoidField, n: N)(implicit dim: ToInt[N]) {
    type SeqType = Sized[Seq[ElementType], N];
    type NSeqType = Newtype[SeqType, SeqOps];

    def CategoryStructure: Monoid[NSeqType] = new Monoid[NSeqType] {
      def empty: NSeqType = apply(
        Sized.wrap[Seq[ElementType], N]((Seq.fill(dim.apply())(monoid.empty)))
      )
      def combine(x: NSeqType, y: NSeqType) = x + y
    }

    abstract class SeqOps(e: SeqType) {
      type Self = Newtype[SeqType, SeqOps];
      def elements = e;
      override def toString = elements.toString;
      def +(other: Self): Self;

    }
    object SeqOps {
      implicit def SeqOps(p: SeqType): SeqOps = new SeqOps(p) {
        def +(other: Self) = newtype(
          zip(elements, other.elements).map((a) => monoid.combine(a._1, a._2))
        );
      }
    }

    def apply(v: SeqType): NSeqType =
      newtype(v)

  }

  class VectorField[N <: Nat, ScalarType](val scalarField: Field[ScalarType], n: N)
    (implicit dim: ToInt[N]) {

    type VectorType = Sized[Seq[ScalarType], N]
    type NVectorType = Newtype[VectorType, VectorOps]

    def AdditiveGroup = new Group[NVectorType] {

      def inverse(x: NVectorType): NVectorType = -x
      def empty: NVectorType = apply(
        Sized.wrap[Seq[ScalarType], N]((Seq.fill(dim.apply())(scalarField.zero)))
      )
      def combine(x: NVectorType, y: NVectorType) = x + y
    }
    // Seq.fill
    // def zero =

    abstract class VectorOps(v: VectorType) {
      type Self = Newtype[VectorType, VectorOps]
      def vector = v
      override def toString = vector.toString
      def +(other: Self): Self;
      def *(scalar: ScalarType): Self;
      def unary_- : Self;
    }

    object VectorOps {
      implicit def pointOps(p: VectorType): VectorOps = new VectorOps(p) {
        def +(other: Self) = newtype(
          zip(vector, other.vector).map((a) => scalarField.plus(a._1, a._2))
        );
        def *(scalar: ScalarType) = newtype(vector.map(v => scalarField.times(v, scalar)))
        def unary_- = newtype(vector.map(scalarField.negate))
      }
    }
    def apply(v: VectorType) =
      newtype[VectorType, VectorOps](v)
  }

  // class PolynomialRing

  class Super {
    def doSomething = {
      implemented
      println(implementedVal)
    };
    def implemented = println("Super");

    val implementedVal = "super val";

    class ImplementedClass {
      val k = "super class field";
    }

  }

  class Subclass extends Super {
    override def implemented: Unit = println("Subclass")
    override val implementedVal: String = "sub val";
    class ImplementedClass extends super.ImplementedClass {}

  }
  def reeeeee() = {
    val k = new Subclass()
    k.doSomething;
    // Nat._0.n
    // val vectorField = new VectorField(doubleScalarField, Nat._4);
    // println(vectorField.AdditiveGroup.empty)
    // val v1 = vectorField(Sized(1.0));
    // val v2 = v1 + v1
    // val extendedHdrs = List("Title", "Author", "ISBN")
    // println(extendedHdrs.sized(_2));
    // extendedHdrs.sized

  }

}
object Main {

  type Eval_t = Double => Double;
  class Functional(val compute: Eval_t) {
    def +(other: Functional) = new Functional((x: Double) => compute(x) + other.compute(x));
    def *(other: Functional) = new Functional((x: Double) => compute(x) * other.compute(x));
    def apply(other: Functional) = new Functional((x: Double) => compute(other.compute(x)));
    def apply(value: Double) = this.compute(value);
  }
  class Differentiable
    (
        override val compute: Eval_t,
        val getDerivative: () => Differentiable
    ) extends Functional(compute) {

    // Summation Rule
    def +(other: Differentiable): Differentiable =
      new Differentiable(
        (x: Double) => compute(x) + other.compute(x),
        () => (this.getDerivative() + other.getDerivative())
      );

    // Product Rule

    def *(other: Differentiable): Differentiable = new Differentiable(
      (x: Double) => compute(x) * other.compute(x),
      () => (this.getDerivative() * other + this * other.getDerivative())
    );
    // Chain Rule
    def apply(other: Differentiable): Differentiable = new Differentiable(
      (x: Double) => compute(other.compute(x)),
      () => (this.getDerivative()(other) * other.getDerivative())
    );

  }

  val zeroF: Differentiable = new Differentiable((x: Double) => 0, () => zeroF);

  implicit def fromConst(value: Double): Differentiable =
    new Differentiable((x: Double) => value, () => zeroF);

  val cosF: Differentiable = new Differentiable(cos, () => sinF);
  val sinF: Differentiable = new Differentiable(sin, () => cosF);
  val expF: Differentiable = new Differentiable(exp, () => expF);
  val X: Differentiable = new Differentiable((x: Double) => x, () => 1);

  def powF: (Double) => Differentiable = (exponent: Double) =>
    if (exponent == 0)
      1
    else
      (new Differentiable(
        (x: Double) => pow(x, exponent),
        () => (exponent * powF(exponent - 1))
      ));

  def main(args: Array[String]): Unit = {
    import Polytopia._;
    Polytopia.main();

    // type Seven = 7
    // // val v = valueOf 

    // class Animal[Legs <: Int with Singleton](implicit v: ValueOf[Legs]) {
    //   def legs = v.value
    // }
    // val reee = new Animal[Seven]
    // println(reee.legs)
    // // val someFn = powF(-1)(expF(X)); // (e^x)^-1
    // val someFn = sinF(cosF(X)) * expF(X) * 2;

    // val someDerivative = someFn.getDerivative();


    // val x = 3;
    // println(someFn(x));
    // println(someDerivative(x));
  }
}


    // trait Addable
    // {
    //     def +(o : Addable) : Addable
    // }

    // def compose[A <: Addable](a : A, b: A) = a + b

    // // compose(1,2)

    // trait Adder[A]{
    //     def add(x: A, y:A) : A
    // }
    // def combine[A](x:A, y:A)(implicit adder : Adder[A]) : A = adder.add(x,y)


    // trait Compose[A, B ,C]
    // {
    //     def compose(a: A, b :B) : C
    // }

    // trait Monoid[A] extends Compose[A, A, A]
    // {
    //     def id : A
    //     override def compose(a :A, b : A) : A
    // }

    // def arrayMultiply[A, B, C](x : Array[A], y : Array[B])
    //     (implicit mult : Compose[A, B, C], add : Monoid[C], c: ClassTag[C])  = 
    //     x.zip(y).map(t => mult.compose(t._1, t._2)).fold(add.id)(add.compose)


    // implicit object AdditiveIntegers extends Monoid[Int]
    // {
    //     def id: Int = 0
    //     override def compose(a: Int, b: Int): Int = a +b
    // }