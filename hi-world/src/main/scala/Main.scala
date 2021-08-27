import math._
object Main {

  type Eval_t = Double => Double;
  class Functional(val compute: Eval_t) {
    def +(other: Functional) = new Functional((x: Double) =>
      compute(x) + other.compute(x)
    );
    def *(other: Functional) = new Functional((x: Double) =>
      compute(x) * other.compute(x)
    );
    def apply(other: Functional) = new Functional((x: Double) =>
      compute(other.compute(x))
    );
    def apply(value: Double) = this.compute(value);
  }
  class Differentiable(
      override val compute: Eval_t,
      val getDerivative: () => Differentiable
  ) extends Functional(compute) {


    // Summation Rule
    def +(other: Differentiable): Differentiable = new Differentiable(
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
    // val someFn = powF(-1)(expF(X)); // (e^x)^-1
    val someFn = sinF(cosF(X))*expF(X) * 2;

    val someDerivative = someFn.getDerivative();

    val x = 3;
    println(someFn(x));
    println(someDerivative(x));
  }
}