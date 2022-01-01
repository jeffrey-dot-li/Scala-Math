package Polytopia

import cc.redberry.rings
import cc.redberry.rings.poly.multivar.MultivariatePolynomial

import rings.poly.PolynomialMethods._
import rings.scaladsl._
import syntax._
import cats.instances.string
import breeze.linalg

import scala.reflect.runtime.universe._
import scala.reflect.ClassTag

object Polytopia {

    implicit class ArrayExt[A](v: Array[A]) {
        def mapWithIndex[B](f: (A, Int) => B)(implicit ct: ClassTag[B]) =
            Array.tabulate(v.length) { i => f(v(i), i) }
    }

    // implicit object AdditivePoly extends Monoid[]

    type Op[T] = T => T;
    type MP[E] = MultivariatePolynomial[E];
    type Cartan = linalg.DenseMatrix[Int]

    type CartanPredicate = (Int, Int) => Int
    type CartanFamily = (Int) => CartanPredicate

    def RootSystems: Map[Char, CartanFamily] = Map(
      'A' -> ((n: Int) =>
          (i: Int, j: Int) =>
              if (i - j == 0) 2
              else if (math.abs(i - j) == 1) -1
              else
                  0
      ),
      'B' -> ((n: Int) =>
          (i: Int, j: Int) =>
              if (i - j == 0) 2
              else if (i == 1 && j == 0) -2
              else if (math.abs(i - j) == 1) -1
              else
                  0
      ),
      'C' -> ((n: Int) =>
          (i: Int, j: Int) =>
              if (i - j == 0) 2
              else if (i == n - 1 && j == n - 2) -2
              else if (math.abs(i - j) == 1) -1
              else
                  0
      )
    )

    def CartanMatrix(dim: Int, c: CartanFamily): Cartan =
        linalg.DenseMatrix.eye[Int](dim).mapPairs((i, v) => c(dim)(i._1, i._2));
    // No idea how this works by the way.

    implicit def function2composable[A, B](f: A => B) = new AnyRef {
        def -->[C](g: B => C) = (v: A) => g(f(v))
    }
    implicit def functionExp[A](f: Op[A]) = new AnyRef {
        def exp(n: Int): A => A = if (n <= 1) f else f --> this.exp(n - 1);
        def **(n: Int) = exp(n)
    }

    def reflect[E](i: Int, roots: Array[MP[E]])(implicit r: MultivariateRing[E]) =
        (m: Monomial[E]) =>
            m.coefficient * r.generators
                .mapWithIndex((x, j) =>
                    if (i != j) x.pow(m.exponents(j))
                    // s_i x_j = x_j
                    else (x - roots(j)).pow(m.exponents(j))
                // s_i x_i = x_i - a_i
                )
                .reduce((a, b) => a * b);

    // def reflect[E](i: Int, c: Cartan)(implicit r: MultivariateRing[E]) =
    //     (m: Monomial[E]) =>
    //         m.coefficient * r.generators.zipWithIndex
    //             .map { case (p, j) =>
    //                 (p - c(i, j) * r.generators(i)).pow((m.exponents)(j))
    //             }
    //             .reduce((a, b) => a * b);

    implicit def PolynomialReduce[E](s: (Monomial[E]) => MP[E]): Op[MP[E]] =
        (p) => p.toArray().map(s).reduce((a, b) => a + b)

    // LMAO cant believe that syntax compiles first try wtf.

    def reflectionRoots[E](cartan: Cartan)(implicit r: MultivariateRing[E], dim: Int) =
        Array
            .ofDim(dim)
            .mapWithIndex((_, i) =>
                cartan.t(::, i).toScalaVector.zip(r.generators).map(t => t._1 * t._2).reduce(r.add)
            )

    def reflections[E](roots: Array[MP[E]])(implicit r: MultivariateRing[E], dim: Int) =
        roots.zipWithIndex.map(i => PolynomialReduce(reflect(i._2, roots)): Op[MP[E]])

    def Differential[E](roots: Array[MP[E]])(implicit r: MultivariateRing[E]) = (s: Op[MP[E]],
                                                                                 i: Int
    ) => ((p: MP[E]) => if (r.isZero(p)) r.zero else (r.divideExact(p - s(p), roots(i)))): Op[MP[E]]

    implicit class MultivariateRingExtension[E](val ring: MultivariateRing[E]) {
        def generators = ring.variables.map((s) => ring(s));
        def dimension = ring.nVariables();
    }

    def Refactor[Poly <: IPolynomial[Poly]](poly: Poly): String = {
        // Safely factor without throwing error on 0
        return (if (poly.isZero) "0" else Factor(poly).toString())
    }

    def main() = {
        implicit val dim = 4;
        val rangle = Array.range(0, dim).map((k) => s"a_$k")
        implicit val ring = MultivariateRing(Q, rangle);
        val rootSystem = RootSystems('C');

        implicit val c: Cartan = CartanMatrix(dim, rootSystem)
        // println(c(::, 0))
        // println(c(::, 1))
        // println(c(::, 2))

        // val cInv = linalg.inv(c);
        // val detC = linalg.det(c).toInt;
        // Bruh
        // println(cInv)
        val x_ = ring.generators

        val a_ = reflectionRoots(c)

        // println(a_.mkString("\n"))

        // println(c)

// Rewrite to have the polynomials based on x_i's not \alpha_i's so then
        // you can write the \alpha_i as a funciton of x_i specifically jsut multiply basis by cartan matrix:
        // \alpha_i = \sum (Cartan Matrix) * (x_i) - x_i
        // Then the switch operator and the Partial operator basically have the same form jsut sub in s(x_i) for both.
        // And then D_i has the same form of 1-\alpha_i / (\sum ...).
        val s = reflections(a_)

// For the fundamental weights, you can convert any integer \alpha_1 ... into x_1 ... by Cartan matrix.
// Which means that x_1 should convert into \alpha_1 ????

        val D = s.zipWithIndex.map { case (refl, index) =>
            Differential(a_)(ring)(refl, index)
        };
        // var masterProduct = ring.one;

        // print(c)

        // val  weightDiffs =  linalg.DenseMatrix.tabulate(3, 3){case (i, j) => D(i)(x_(j))}

        // println(weightDiffs)

        val p1 = D(0)
        val p2 = D(0) --> D(1) --> D(0);
        val p3 = D(0) --> D(1) --> D(2) --> D(3)  --> D(2) --> D(1) --> D(0)
        // val p4 = D(0) -> D

        println((D(0))(x_(0)^7))
        // val p3 = D(0) --> D(1) --> D(2) --> D(1) --> D(0);
        // println(D(0)( x_(0)^5 ))

        // val k = s(1) --> s(0)
        // println(Refactor((  D(0)(x_(2))   )))
        // println(Refactor(x_(0)))
        // print(Refactor((D(1))(v_(2) * v_(1))))
        // print(Refactor(D(1)(v_(2)) * v_(1) + s(1)(v_(2)) * D(1)(v_(1))))
    }

}
