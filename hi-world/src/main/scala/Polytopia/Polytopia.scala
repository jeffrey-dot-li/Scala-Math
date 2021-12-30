package Polytopia

import cc.redberry.rings
import cc.redberry.rings.poly.multivar.MultivariatePolynomial

import rings.poly.PolynomialMethods._
import rings.scaladsl._
import syntax._
import cats.instances.string

import breeze.linalg

object Polytopia {
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
              else if (i == 0 && j == 1) -2
              else if (math.abs(i - j) == 1) -1
              else
                  0
      )
    )

    def CartanMatrix(dim: Int, c: CartanFamily): Cartan =
        linalg.DenseMatrix.eye[Int](dim).mapPairs((v, dim) => c(dim)(v._1, v._2));
    // No idea how this works by the way.

    implicit def function2composable[A, B](f: A => B) = new AnyRef {
        def -->[C](g: B => C) = (v: A) => g(f(v))
    }
    implicit def functionExp[A](f: Op[A]) = new AnyRef {
        def exp(n: Int): A => A = if (n <= 1) f else f --> this.exp(n - 1);
        def **(n: Int) = exp(n)
    }

    // def reflect[E](i: Int, c: Cartan)(implicit r: MultivariateRing[E]) =
    //     (m: Monomial[E]) =>
    //         m.coefficient * r.generators.zipWithIndex
    //             .map { case (p, j) =>
    //                 (p - c(i, j) * r.generators(i)).pow((m.exponents)(j))
    //             }
    //             .reduce((a, b) => a * b);

    def reflect[E](i: Int, c: Cartan)(implicit r: MultivariateRing[E]) =
        (m: Monomial[E]) =>
            m.coefficient * r.generators.zipWithIndex
                .map { case (p, j) =>
                    (p - c(i, j) * r.generators(i)).pow((m.exponents)(j))
                }
                .reduce((a, b) => a * b);

    implicit def PolynomialReduce[E](s: (Monomial[E]) => MP[E]): Op[MP[E]] =
        (p) => p.toArray().map(s).reduce((a, b) => a + b)
// LMAO cant believe that syntax compiles first try wtf.

    def reflections[E](n: Int, c: Cartan, r: MultivariateRing[E]) =
        Array.range(0, n).map(i => PolynomialReduce(reflect(i, c)(r)): Op[MP[E]])

    def Differential[E](implicit r: MultivariateRing[E]) = (s: Op[MP[E]], i: Int) =>
        ((p: MP[E]) => if (r.isZero(p)) r.zero else (r.divideExact(p - s(p), r.generators(i)))): Op[MP[E]]

    implicit class MultivariatePolynomialExtension[E](p: MP[E]) {

        def swappers(i: Int, j: Int) = p.swapVariables(i, j);
        def TD(i: Int, j: Int)(implicit r: MultivariateRing[E]): MP[E] = {
            val swapped = swappers(i, j);
            val s = r.divideAndRemainder(p - swapped, (r.generators(i) - r.generators(j)))
            val div = s(0);
            val rem = s(1);
            // val (div, rem) = swapped /% (r.generators(i) - r.generators(j));
            if (rem != r.zero) {
                println("REEE NOT ZERO")
                println(Factor(rem));
                println("REE");
            }
            return div;
        }
    }

    implicit class MultivariateRingExtension[E](val ring: MultivariateRing[E]) {
        def generators = ring.variables.map((s) => ring(s));
        def dimension = ring.nVariables();
    }

    def Refactor[Poly <: IPolynomial[Poly]](poly: Poly): String = {
        // Safely factor without throwing error on 0
        return (if (poly.isZero) "0" else Factor(poly).toString())
    }

    def Diracket[E](p: MP[E])(i: Int, j: Int, k: Int)(implicit r: MultivariateRing[E]): MP[E] = {
        val k1 = p.TD(k, j).TD(j, i);
        val k2 = p.TD(j, i).TD(k, j);
        println(s"Diracket:  ${(k1)} - ${(k2)}  ")
        return k1 - k2
    }
    def DoubleDiff[E](p: MP[E])(i: Int, j: Int, k: Int)(implicit r: MultivariateRing[E]): MP[E] = {
        val p1 = p.TD(j, k);
        val p2 = p1.TD(i, j);
        println(s"p: ${Refactor(p)} => ${Refactor(p1)} => ${Refactor(p2)}  ")
        return p2
    }

    def COB = (s: (Int, Int, Int)) =>
        ((s._1 - s._2 + s._3), (s._2 - s._3 + s._1), (s._3 - s._1 + s._2));

    def COBBack = (s: (Int, Int, Int)) => ((s._1 + s._2) / 2, (s._2 + s._3) / 2, (s._3 + s._1) / 2);
    // def

    def main() = {
        val dim = 3;
        val rangle = Array.range(0, dim).map((k) => s"a_$k")
        implicit val ring = MultivariateRing(Q, rangle);
        val rootSystem = RootSystems('C');

        implicit val c: Cartan = CartanMatrix(dim, rootSystem)
        val cInv = linalg.inv(c);
        val detC = linalg.det(c).toInt;
        // Bruh
        // println(cInv)
        val v_ = ring.generators

        val x_ = Array.range(0,dim).map(i =>
            v_.zip(cInv(::, i).toScalaVector())
                .map(t2 =>
                    (
                      ring.multiplyConstant(t2._1, (Q((detC * t2._2).toInt) / Q(detC)))
                    )
                )
                .reduce((a, b) => a + b)
        );
		// println(x_.mkString("\n"))
		
		// println(cInv(::,0).toScalaVector())
		// print("fuck")

// Rewrite to have the polynomials based on x_i's not \alpha_i's so then 
	// you can write the \alpha_i as a funciton of x_i specifically jsut multiply basis by cartan matrix:
	// \alpha_i = \sum (Cartan Matrix) * (x_i) - x_i
	// Then the switch operator and the Partial operator basically have the same form jsut sub in s(x_i) for both.
	// And then D_i has the same form of 1-\alpha_i / (\sum ...).
    val s = reflections(dim, c, ring)

 
// For the fundamental weights, you can convert any integer \alpha_1 ... into x_1 ... by Cartan matrix.
// Which means that x_1 should convert into \alpha_1 ????

        val D = s.zipWithIndex.map { case (refl, index) => Differential(ring)(refl, index) };
        var masterProduct = ring.one;

        // print(c)

		// val  weightDiffs =  linalg.DenseMatrix.tabulate(3, 3){case (i, j) => D(i)(x_(j))}

		// println(weightDiffs)

		val p3 = D(0) --> D(1) --> D(2) --> D(1) --> D(0);

		println(D(0)( x_(0)^5 ))

        // val k = s(1) --> s(0)
		// println(Refactor((  D(0)(x_(2))   )))
		// println(Refactor(x_(0)))
        // print(Refactor((D(1))(v_(2) * v_(1))))
        // print(Refactor(D(1)(v_(2)) * v_(1) + s(1)(v_(2)) * D(1)(v_(1))))
    }

}
