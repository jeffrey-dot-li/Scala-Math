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
    type Cartan = linalg.DenseMatrix[Int];
    type Chain = Array[Int];

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
    implicit def opArray2Op[A](arr: Array[Op[A]]): Op[A] = arr.reduce((a, b) => a --> b)

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
        implicit val dim = 4;
        val rangle = Array.range(0, dim).map((k) => s"a_$k")
        implicit val ring = MultivariateRing(Q, rangle);
        val rootSystem = RootSystems('F');

        implicit val c: Cartan = CartanMatrix(dim, rootSystem)

        val id = (x: ring.PolyType) => x
        val x_ = ring.generators
        val a_ = reflectionRoots(c)
        val s = reflections(a_)
        val y_ = x_.mapWithIndex((x, i) => s(i)(x))

        val D = s.mapWithIndex((refl, index) => Differential(a_)(ring)(refl, index));

        val xd = Array(Array(0), Array(1), Array(2), Array(3));
        def getPermutations(n: Int): Array[Array[Int]] = {
            if (n == 1) return xd
            else {
                val prev = getPermutations(n - 1)
                return xd.map(k => prev.map(s => s ++ k)).reduce((a, b) => a ++ b)
            }
        }

        // println(getPermutations(1).length)
        // println(getPermutations(2).length)

        def doTestingThings(p: ring.PolyType) : Array[Array[Int]] = {
            var ones = Array[Array[Int]]()
            for (chain <- getPermutations(p.degree())) {
                val dunno = opArray2Op(chain.map(i => D(i)))
                val result = dunno(p)
                if (result == ring.one) {
                    ones = ones :+ chain;
                }
            }
            return ones;
        }

        val maxs = Array[ring.PolyType](
            (x_(0)^1) * (x_(1)^2),
            (x_(2))^4,
            (x_(3))^6
        );

        // val maxsOnesTested = maxs.map(doTestingThings)
        // for(icu <- 0 until maxs.length)
        // {
        //     val chainOfChains = maxsOnesTested(icu)
        //     if(chainOfChains.length == 0)
        //     {
        //         println("YAY INDEX :" + icu)
        //     }
        //     else
        //         {
        //             println("FUCK INDEX: " + icu)
        //             println(chainOfChains.length)
        //             println(chainOfChains(0).mkString(" "))
        //         }
        // }

        // var chains = Array[Chain](
        //     Array(0),
        //     Array(0,1),
        //     Array(2,1,2),
        //     Array(3,2,1,2,3)
        // );

        def PartialChain(ch: Chain) = ch.map(D);
        def MonoChain(ch: Chain) = (x_(ch.last) ^ (ch.length));
        var chains = Array[Chain](
          Array(1, 0),
          Array(1),
          Array(2, 1, 2),
          Array(3, 2, 1, 2, 3)
        );
        var monos = chains.map(MonoChain)
        var partialChains = chains.map(PartialChain);
        // println(partialChains(0)(monos(0)))

        // var weirdBoi = id --> partialChains(0) --> (partialChains(3)) --> (partialChains(2)) --> (partialChains(1))
        // var total = monos.reduce((a, b) => a*b);
        // println(weirdBoi(total)) - reduces to 1

        // var andy = D(2) --> D(1);
        // println(andy(x_(1)^2)) // D1 D2 x_1^2 when x_1 > x_2 reduces to 2

        // var randy = Array(0,1,2)
        // println("randy: " + PartialChain(randy)(MonoChain(randy) ));

        // var sandy = Array(2,1,2,3)
        // println("sandy: " + PartialChain(sandy)(MonoChain(sandy) ));

        val sM = s.mapWithIndex((_, i) =>
            linalg.DenseMatrix
                .eye[Int](dim)
                .mapPairs((p, v) =>
                    if (p._2 == i)
                        if (p._1 == p._2) -1
                        else -c(p._2, p._1)
                    else if (p._1 == p._2) 1
                    else 0
                )
        );

        
        // switch operators as matrix on basis of x_i

        val xV = x_.mapWithIndex((_, i) =>
            linalg.DenseVector
                .zeros[Double](dim)
                .mapPairs((j, _) =>
                    if (i == j) 1
                    else 0
                )
        )

        println(sM(0))
        println(" ")
        println(sM(1))
        println(" ")
        // println(sM(2))
        // println(" ")
        // println(sM(3))
        // println(" ")
        println(sM(0)*sM(1));
        println(" ")

        println(sM(1)*sM(0)*sM(1));
        println(" ")
        
        println(sM(1)*sM(0));
        println(" ") 
        

        

        // D(i) M x(j) = M(i,j)

        // println((s(1) --> s(2) --> s(1))(x_(1)))

        // println(sM(1) * sM(2) *sM(1) * xV(1))

        val mId = linalg.DenseMatrix.eye[Int](dim);

        // if s_i s_2 s_j has a -1 in any row row k
        // then \partial_k \partial_i \partial_j = 0
        type mOp = linalg.DenseMatrix[Int]
        type ZooResident = (Chain, mOp)
        var zoo = Array[ZooResident]()
        val zooEntrance = collection.mutable.PriorityQueue.empty[(Chain, mOp)](Ordering.by((_:(Chain, mOp))._1.length).reverse)
        zooEntrance.addOne((Array[Int](), mId));

        var negCount = 0
        var dupCount = 0;

        while(zooEntrance.nonEmpty)
        {
            val moo = zooEntrance.dequeue()
            val found = zoo.find((k) => k._2 == moo._2)
            if(found != None)
            {
                dupCount+=1;
            }
            if(found == None)
            {
                zoo +:= moo

                for(i <- 0 until dim)
                {
                    // if(sM(i) * moo._2 != moo._2 * sM(i))
                    // {
                    // }
                    val ithRow = moo._2(i,::);
                    // val hasNeg = false
                    val hasNeg = ithRow.t.toScalaVector().find((k) => (k < 0)) != None;
                    if(hasNeg)
                    {
                        negCount+=1;
                    }
                    if(!hasNeg)
                    {
                        val k = (i +: moo._1,  sM(i) * moo._2)
                        zooEntrance+= k
                    }
                }
            }
        }
        println("negatives: " + negCount + " dups: " + dupCount)

        /** Theory - chain (K) len (r) is zero iff there is other chain (K2) with len (r2) so that
          * s_K = s_K2 but r > r2.
          *
          * D_K = 0 IFF <-> K is non-minimal / reducible. IFF len(K) > height(s_K)
          *
          * So then if you have D_i on the matrix with negative numbers it means that there is
          * smaller chain that produces the same reflection in the Weyl group.
          *
          * Like basically the negative number in whatever ith row is telling you basically that its
          * already reflection conjugate under s_i
          *
          * Like for example s_1 (s_2 s_1 s_2) = s_2 s_1
          *
          * For the ones with negative in the row - does s_i positive it?
          *
          * Theorem - if you apply s_i on a chain matrix where there is neg in ith row, Then there
          * is smaller K2 which gives you same refl group element.
          *
          * // println("negatives: " + negCount + " dups: " + dupCount)
          *
          * 2304 negatives (2 * 1152) and 1153 dups (1152 + 1)
          * --> The +1 comes from because you first populate the zooEntrance with Identity, so it
          * double counts Id, and thats all.
          *
          * negs is where you have an equal chain of strictly smaller size dups is then where you
          * have an equal chain of strictly equal size
          *
          * Without the (hasNeg) filter, you get 3458 (= 1154 + 2304) dups. Which means that every
          * single chain that failed the hasNeg filter was a dup. hasNeg therefore must be the same
          * thing as <--> !irreducible
          *
          * Assume you have chain K_r. Assume D_j s_K x_i < 0 for some i, j. Assume S(K_r) {i,j}
          * element at {i,j} in the S(K_r) matrix is negative Then s_j S(K_r) = S(K_r2) for some
          * chain K_r2 with r2 < r1.
          */

        // var tested = 0;
        // for(w <- zoo)
        // {
        //     for(i <- 0 until dim)
        //     {
        //         var negTested = false;
        //         for(j <- 0 until dim)
        //         {
        //             if(w._2(i,j) < 0 && !negTested)
        //             {
        //                 val sw = sM(i) * w._2;
        //                 val minimal = zoo.find(k => k._2 == sw);
        //                 if(minimal==None)
        //                 {
        //                     throw new Exception("reeeee")
        //                 }
        //                 else
        //                 {
        //                     if(w._1.length  > minimal.get._1.length)
        //                     {
        //                         // yay
        //                         negTested = true;
        //                         tested+=1;
        //                     }
        //                     else
        //                         {
        //                             println("FUCKKKK")
        //                             println("i: " + i)
        //                             println("w: " + w._1.mkString(" "))
        //                             println("wmin: " + minimal.get._1.mkString(" "))
        //                             throw new Exception("FUCKKKKKKKKK")
        //                         }
        //                 }
        //                 // if(minimal != None && minimal.)
        //             }
        //         }
        //     }
        // }
        // println(" YAY : " + tested )
        // println(zoo.length)
        // // zoo.
        // println(zoo(0)._1.mkString(" "))
        // println(zoo(0)._1.length)

        // val row0s = zoo.map((k) => k._2.t(::,0)).distinct
        // println(row0s.length)
        // println(row0s.mkString("\n"))
        // println(zoo(4))
        // print(row0s(4))

        // println((mId - sM(1))*sM(0))

        // Theory - if p is unimodular, then every factor of p is also unimodular

    }

}
