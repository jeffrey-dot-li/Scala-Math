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
import org.apache.commons.math3.analysis.function.Add

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
      ),
      'K' ->
          //   Same as C except the first root is longer than the rest instead of the last being the longest
          ((n: Int) =>
              (i: Int, j: Int) =>
                  if (i - j == 0) 2
                  else if (i == 0 && j == 1) -2
                  else if (math.abs(i - j) == 1) -1
                  else
                      0
          ),
      'F' ->
          ((n: Int) =>
              (i: Int, j: Int) =>
                  if (i == 1 & j == 2) -2
                  else if (i - j == 0) 2
                  else if (math.abs(i - j) == 1) -1
                  else 0
          )
    )

    def CartanMatrix(dim: Int, c: CartanFamily): Cartan =
        linalg.DenseMatrix.eye[Int](dim).mapPairs((i, v) => c(dim)(i._1, i._2));
    // No idea how this works by the way.

    implicit def function2composable[B, C](f: B => C) = new AnyRef {
        def -->[A](g: A => B) = (v: A) => f(g(v))
    }
    implicit def functionExp[A](f: Op[A]) = new AnyRef {
        def exp(n: Int): A => A = if (n <= 1) f else f --> this.exp(n - 1);
        def **(n: Int) = exp(n)
    }

    implicit def p2O[E](p: MP[E]): Op[MP[E]] = (x) => x * p;

    implicit def polyWrapper[E](p: MP[E]) = new AnyRef {
        def -->(op: Op[MP[E]]): Op[MP[E]] = (x) => p * op(x)
        // def *[Op[MP[E]]](op : Op[MP[E]]) : Op[MP[E]] = (x) => p * op(x)
    }
    implicit def operatorMult[E](op: Op[MP[E]]) = new AnyRef {
        def *(s: MP[E]): Op[MP[E]] = (x) => op(s * x)
        def +(op2: Op[MP[E]]): Op[MP[E]] = x => op(x) + op2(x)
        def unary_- : Op[MP[E]] = x => -op(x)
        def -(op2: Op[MP[E]]): Op[MP[E]] = x => op(x) - op2(x)
    }

    def Diracket[E](p: Op[MP[E]], q: Op[MP[E]]): Op[MP[E]] = (p --> q) - (q --> p)
    def Addracket[E](p: Op[MP[E]], q: Op[MP[E]]): Op[MP[E]] = (p --> q) + (q --> p)

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
        implicit val dim = 5;
        val rangle = Array.range(0, dim).map((k) => s"a_$k")
        implicit val ring = MultivariateRing(Q, rangle);
        val rootSystem = RootSystems('K');

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
        val s = reflections(a_)
        val y_ = x_.mapWithIndex((x, i) => s(i)(x))

        val D = s.zipWithIndex.map { case (refl, index) =>
            Differential(a_)(ring)(refl, index)
        };
        // var masterProduct = ring.one;

        // print(c)

        // val  weightDiffs =  linalg.DenseMatrix.tabulate(3, 3){case (i, j) => D(i)(x_(j))}

        // println(weightDiffs)

        var monos = Array.ofDim[Int](dim).mapWithIndex((_, i) => x_(i) ^ (2 * i + 1))
        var chains = Array.ofDim[Int](dim).mapWithIndex((_, i) => D(i))
        for (i <- 1 until dim) {
            chains(i) = (D(i) --> chains(i - 1) --> D(i))
        }
        var sumBrackets = Array
            .ofDim[Int](dim)
            .mapWithIndex((_, i) =>
                (p: ring.PolyType) => chains(i)(x_(i) * p) + x_(i) * chains(i)(p)
            )

        // println(( D(3) --> chains(2))( x_(2)* D(3)(monos(3)) ))
        //
        // println(sumBrackets(1)(monos(1)))
        // println(sumBrackets(0)(monos(0)))
        val id = (x: ring.PolyType) => x

        // x_i k_i + k_i x_i (x_i)^{2i-1} = x_i + 2i x_{i+1}
        val targetK = (i: Int) => chains(i) --> x_(i)
        // print("Target: ")
        // println(targetK(1)(monos(1)))

        // val step = (i:Int) => D(i) --> chains(i-1) --> D(i) --> x_(i)
        // val step = (i:Int) => D(i) --> chains(i-1) --> (p2O(y_(i)) --> D(i)  + id)
        // val step = (i:Int) => D(i) --> chains(i-1) --> (p2O(x_(i-1) - x_(i)  + x_(i+1)) --> D(i)  + id)
        // val step = (i:Int) => (x_(i+1) --> chains(i)) - (D(i)-->x_(i) -->chains(i-1)-->D(i))+ (D(i) --> chains(i-1) --> x_(i-1) --> D(i)) + (D(i) --> chains(i-1) )
        // val step = (i:Int) => (x_(i+1) --> chains(i)) - ((y_(i) --> D(i) + id) -->chains(i-1)-->D(i))+ (D(i) --> chains(i-1) --> x_(i-1) --> D(i)) + (D(i) --> chains(i-1) )
        // var step = (i:Int) => ((x_(i+1) - y_(i)) --> chains(i)) - (chains(i-1)-->D(i)) + (D(i) --> chains(i-1) --> x_(i-1) --> D(i)) + (D(i) --> chains(i-1) )
        // var step = (i:Int) => ((x_(i) - x_(i-1)) --> chains(i)) + (D(i) --> chains(i-1) --> x_(i-1) --> D(i)) + (D(i) --> chains(i-1) ) - (chains(i-1)-->D(i))
        // var step = (i:Int) => ((x_(i) - x_(i-1)) --> chains(i)) + (D(i) --> (Diracket(chains(i-1), x_(i-1)) + (x_(i-1) --> chains(i-1))) --> D(i)) + (D(i) --> chains(i-1) ) - (chains(i-1)-->D(i))
        // var step = (i:Int) => ((x_(i) - x_(i-1)) --> chains(i)) +  (x_(i-1) --> chains(i))  + (D(i) --> (Diracket(chains(i-1), x_(i-1))) --> D(i)) + (D(i) --> chains(i-1) ) - (chains(i-1)-->D(i))
        var step = (i: Int) =>
            ((x_(i)) --> chains(i)) + (D(i) --> (Diracket(chains(i - 1), x_(i - 1))) --> D(i)) + (D(
              i
            ) --> chains(i - 1)) - (chains(i - 1) --> D(i))

        // println(x_(2)- y_(1))
        // print("step: ")
        // println(step(1)(monos(1)))

        val stepNumber = 3

        val dirac0 = (2 * (x_(1) - x_(0)) --> D(0)) + id
        // [k_0 x_0 - x_0 k_0]

        val targetDirac = (i: Int) => Diracket(chains(i), x_(i))

        // print(f"Target ${stepNumber}:")
        // println(targetDirac(stepNumber)(monos(stepNumber)))

        // var dirac1Step = (D(1) --> dirac0 --> D(1)) + Diracket(D(1), chains(0))
        // var dirac1Step = (D(1) --> 2*(x_(1) - x_(0)) --> D(0)  --> D(1)) + Diracket(D(1), chains(0))
        // var dirac1Step = ((D(1) --> x_(1) --> D(0)  --> D(1)) - (x_(0) --> chains(1)))*2 + Diracket(D(1), chains(0))
        // var dirac1Step = ((((y_(1) --> D(1)) + id) --> D(0)  --> D(1)) - (x_(0) --> chains(1)))*2 + Diracket(D(1), chains(0))
        // var dirac1Step = (( D(0)  --> D(1)) + ((y_(1) - x_(0)) --> chains(1)))*2 + Diracket(D(1), chains(0))
        // var dirac1Step = (( D(0)  --> D(1)) + ((x_(2)- x_(1)) --> chains(1)))*2 + Diracket(D(1), chains(0))
        // var dirac1Step = ( D(0)  --> D(1))*2 + ((x_(2)- x_(1)) --> chains(1))*2 + Diracket(D(1), chains(0))
        var dirac1 = (((x_(2) - x_(1)) --> chains(1)) * 2 + Addracket(D(1), chains(0)))
        // [k_1 x_1 - x_1 k_1]

        // var

        // var dirac2Step =  (D(2) --> dirac1 --> D(2)) + Diracket(D(2), chains(1))
        // var dirac2Step =  (D(2) --> (((x_(2)- x_(1)) --> chains(1))*2 + Addracket(D(1), chains(0))) --> D(2)) + Diracket(D(2), chains(1))
        // var dirac2Step =  (D(2) --> (((x_(2)- x_(1)) --> chains(1))*2 + Addracket(D(1), chains(0))) --> D(2)) + Diracket(D(2), chains(1))
        var dirac2Step = ((2 * (x_(3) - x_(2))) --> chains(2)) + Addracket(D(2), chains(1)) + (D(
          2
        ) --> Addracket(D(1), chains(0)) --> D(2))
        // var dirac2Step = Addracket(D(2), chains(1)) + (D(2) --> Addracket(D(1), chains(0)) --> D(2))
        var dirac3Step = Addracket(D(3), chains(2))

        // print(s"D Step ${stepNumber}:")
        // println(dirac3Step(monos(3)))
        // should be equal to (k_i x_i p)

        // println(kp(1)(monos(1)))

        // println((D(1)--> D(0))(x_(0)* D(1)(x_(1)^3)))

        println("HII")

        def reeChain(i: Int): Op[ring.PolyType] = {
            var ree = D(0);
            for (j <- 0 until i) {
                var k = i - j
                ree = ree --> D(k)
            }
            for (j <- 2 to i) {
                ree = ree --> D(j)
            }
            return ree
        }

        // reeChain(2)
        println((D(1) --> D(2))(x_(2) ^ 5))
        println((D(2) --> D(1) --> D(2))(x_(2) ^ 5))

        // println(reeChain(2)(x_(2)^5))

        // // println((chains(2)) (monos(2) * x_(2)))
        // // K3 (x3^6)
        // println((chains(1)) (y_(2)* D(2)(monos(2))))
        // println((chains(1)) ( D(2)(monos(2))))

        // // K2 (y3 * D3 x3^5)
        // // 4z3z4 + 2(z3)^2 - 2 z2 z3
        // // (2i-2)x_(i)x_i+1 + 2 (x_i)^2 - 2 x_(i-1)x_i

        // println((chains(1)) (x_(1)* D(2)(monos(2))))
        // println((chains(1)) ((-x_(2)+x_(3))* D(2)(monos(2))))

        // // K2 (-x3 * D3 x3^5)
        // //
        // println((D(2) --> chains(1)) (y_(2)* D(2)(monos(2))))
        // D3 K2 (y3 * D3 x3^5)

        // println(chainer(3)._1 (chainer(3)._2))

        // for(i <- chainer)
        // {
        //     print(i._2)
        //     print(" ")
        // }

        // println(y_(3))
        // println((chainer(2)._1)(y_(3)^5))
        /** [ (d_0, x_0), (d_1 d_0 d_1, x_1^3), ... ]
          */
        // val p1 = D(0)
        // val p2 = D(0) --> D(1) --> D(0);
        // val p3 = D(0) --> D(1) --> D(2) --> D(3) --> D(2) --> D(1) --> D(0)
        // val p4 = D(0) -> D

        // println((D(0))(x_(0) ^ 7))
        // val p3 = D(0) --> D(1) --> D(2) --> D(1) --> D(0);
        // println(D(0)( x_(0)^5 ))

        // val k = s(1) --> s(0)
        // println(Refactor((  D(0)(x_(2))   )))
        // println(Refactor(x_(0)))
        // print(Refactor((D(1))(v_(2) * v_(1))))
        // print(Refactor(D(1)(v_(2)) * v_(1) + s(1)(v_(2)) * D(1)(v_(1))))
    }

}
