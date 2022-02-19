package polytopia

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

object Main {
    def printArray[A](v: Array[A]) = println(v.mkString(" "));
    def printlnArray[A](v: Array[A]) = println(v.mkString("\n \n"));

    implicit class ArrayExt[A](v: Array[A]) {
        def mapWithIndex[B](f: (A, Int) => B)(implicit ct: ClassTag[B]) =
            Array.tabulate(v.length) { i => f(v(i), i) }
    }

    implicit class MatrixExt(c: Cartan) {
        def colRepr = Array.tabulate(c.cols)(i => c(::, i))
        def rowRepr = c.t.colRepr;
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
      'C' ->
          //   First root is longest, rather than the last root from Bourbaki.
          ((n: Int) =>
              (i: Int, j: Int) =>
                  if (i - j == 0) 2
                  else if (i == 0 && j == 1) -2
                  else if (math.abs(i - j) == 1) -1
                  else
                      0
          ),
      'D' ->
          // The first node is adjacent to node 3, rest is same as A_(n-1)
          // Inverted from Bourbaki
          ((n: Int) =>
              (i: Int, j: Int) =>
                  if (i - j == 0) 2
                  else if (i == 0 || j == 0)
                      if (i == 2 || j == 2) -1 else 0
                  else if (math.abs(i - j) == 1) -1
                  else
                      0
          ),
      'E' ->
          ((n: Int) =>
              (i: Int, j: Int) =>
                  if (i - j == 0) 2
                  else if (i == 0 || j == 0)
                      if (i == 3 || j == 3) -1 else 0
                  // The first node is adjacent to node 4, rest is same as A_(n-1)
                  // Inverted from Bourbaki
                  else if (math.abs(i - j) == 1) -1
                  else 0
          ),
      'F' ->
          ((n: Int) =>
              (i: Int, j: Int) =>
                  if (i == 1 & j == 2) -2
                  else if (i - j == 0) 2
                  else if (math.abs(i - j) == 1) -1
                  else 0
          ),
      'G' ->
          //   First root is longest, rather than the last root from Bourbaki.
          ((n: Int) =>
              (i: Int, j: Int) =>
                  if (i - j == 0) 2
                  else if (i == 0 && j == 1) -3
                  else if (math.abs(i - j) == 1) -1
                  else
                      0
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

    // Conjecture testing on matrix representations of (F4) Weyl Group.
    val baseArray = Array(Array(0), Array(1), Array(2), Array(3));

    /** Generates `n` matrices of dimension `n x n` corresponding to the Weyl Group reflections
      * generators `s_i` in the basis `x_i`.
      *
      * @param c
      *   Cartan Matrix of Weyl Group
      * @return
      *   Array[Matrix] - n length array of n x n integer matrixes - integer if group is
      *   semi-simple.
      */
    def genReflectionMatrixs(c: Cartan): Array[Cartan] = {
        return Array.tabulate(c.cols)((i) =>
            linalg.DenseMatrix
                .eye[Int](c.cols)
                .mapPairs((p, v) =>
                    if (p._2 == i)
                        if (p._1 == p._2) -1
                        else -c(p._2, p._1)
                    else if (p._1 == p._2) 1
                    else 0
                )
        )
    }

    def genWeylGroupMatrixs(dim: Int, sM: Array[Cartan], max: Int = Int.MaxValue)
        : Array[(Chain, Cartan)] = {

        val mId = linalg.DenseMatrix.eye[Int](dim);

        type mOp = linalg.DenseMatrix[Int]

        // Tuple of Weyl Chain and corresponding Matrix Representation.
        type ZooResident = (Chain, mOp)
        var zoo = Array[ZooResident]()
        val zooEntrance = collection.mutable.PriorityQueue
            .empty[(Chain, mOp)](Ordering.by((_: (Chain, mOp))._1.length).reverse)
        zooEntrance.addOne((Array[Int](), mId));

        var negCount = 0
        var dupCount = 0;

        while (zooEntrance.nonEmpty && zoo.length <= max) {
            val moo = zooEntrance.dequeue()
            val found = zoo.find((k) => k._2 == moo._2)
            if (found != None) {
                dupCount += 1;
            }
            if (found == None) {
                zoo +:= moo

                for (i <- 0 until dim) {
                    val ithRow = moo._2(i, ::);
                    val hasNeg = ithRow.t.toScalaVector().find((k) => (k < 0)) != None;
                    if (hasNeg) {
                        negCount += 1;
                    }
                    if (!hasNeg) {
                        val k = (i +: moo._1, sM(i) * moo._2)
                        zooEntrance += k
                    }
                }
            }
        }
        println(dupCount + negCount)
        return zoo;
    }

    def getPermutations(n: Int): Array[Array[Int]] = {
        if (n == 1) return baseArray
        else {
            val prev = getPermutations(n - 1)
            return baseArray.map(k => prev.map(s => s ++ k)).reduce((a, b) => a ++ b)
        }
    }

    def testZooResidents() {}

    def main(): Unit = {

        implicit val dim = 4;
        val rootSystem = RootSystems('F');
				//  Conjecture: G3+ is infinite? F5+, E9+ also infinite?
				// Trying to generate the G3 matrices will give you a group with infinite order?

        val rangle = Array.range(0, dim).map((k) => s"a_$k")
        implicit val ring = MultivariateRing(Q, rangle);

        implicit val c: Cartan = CartanMatrix(dim, rootSystem)

        val id = (x: ring.PolyType) => x
        val x_ = ring.generators
        val a_ = reflectionRoots(c)
        val s = reflections(a_)
        val y_ = x_.mapWithIndex((x, i) => s(i)(x))

        val D = s.mapWithIndex((refl, index) => Differential(a_)(ring)(refl, index));

        def PartialChain(ch: Chain) = ch.map(D);
        def MonoChain(ch: Chain) = (x_(ch.last) ^ (ch.length));

        // Maximal chains in F4.
        // var chains = Array[Chain](
        //   Array(1, 0),
        //   Array(1),
        //   Array(2, 1, 2),
        //   Array(3, 2, 1, 2, 3)
        // );
        // var monos = chains.map(MonoChain)
        // var partialChains = chains.map(PartialChain);

        // Matrix representation of reflections in `x_i`.
        val sM = genReflectionMatrixs(c);

        // Column vector representations of `x_i`
        val xV = x_.mapWithIndex((_, i) =>
            linalg.DenseVector
                .zeros[Double](dim)
                .mapPairs((j, _) =>
                    if (i == j) 1
                    else 0
                )
        )

        // Weyl Group matrix representation
        val wM = genWeylGroupMatrixs(dim, sM, 1500);

        // Checks that in all matrixes of the Weyl Representation,
        // each row is either positive or negative semidefinite.
        // There are no rows that contain both positive and negative numbers.

        // Checked for An, Bn, Cn, Dn, F4, G2 | n <= 4.

				// Also checked for G3, E6, F5 |W| <= 1500
        def checkSemiDefinite(m: Cartan): Boolean = {
            for (row <- m.rowRepr) {
                var numRep = 0;
                for (j <- row) {
                    if (j < 0) {
                        if (numRep > 0) return false;
                        numRep = -1;
                    }
                    if (j > 0) {
                        if (numRep < 0) return false;
                        numRep = 1;
                    }
                }
            }
            return true;
        }
        val res = polytopia.TestUtils.runTests(wM, (k: (Chain, Cartan)) => checkSemiDefinite(k._2));
        println("passed: " + res.status + " num tested: " + res.numTested)
    }

}
