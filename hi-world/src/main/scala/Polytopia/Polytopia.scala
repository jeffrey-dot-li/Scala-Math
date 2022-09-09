package polytopia

import cc.redberry.rings
import cc.redberry.rings.poly.multivar.MultivariatePolynomial

import rings.poly.PolynomialMethods._
import rings.scaladsl._
import syntax._
import cats.instances.string
import breeze.linalg
import scala.io.StdIn;
import scala.util.control._

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
        // Access ith row with c(i,::) and jth col with c(::, j)
        def rowRepr = Array.tabulate(c.rows)(i => c(i, ::));
        def colRepr = Array.tabulate(c.cols)(j => c(::, j));
        // def COB(cM: Cartan) = linalg.inv(cM)*c*cM;
    }

    def ColVector(dim: Int)(i: Int) = linalg.DenseVector.tabulate(dim)(j => if (j == i) 1 else 0)
    def RowVector(dim: Int)(i: Int) = ColVector(dim)(i).t;

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
          //   First Root Shortest
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
      //   root 2 is longer than root 3, -2 is upper right
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
                        else -c(p._1, p._2)
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
        // println(dupCount + negCount)
        return zoo;
    }

    def getPermutations(n: Int): Array[Array[Int]] = {
        if (n == 1) return baseArray
        else {
            val prev = getPermutations(n - 1)
            return baseArray.map(k => prev.map(s => s ++ k)).reduce((a, b) => a ++ b)
        }
    }

    // def

    def printMatrixMult(c1: Cartan, c2: Cartan): Cartan = {
        println();
        val prodr = (c1 * c2).toString.split("\n");
        val c1r = c1.toString.split("\n");
        val c2r = c2.toString.split("\n");

        // c1.rowRepr(0).toArray

        val spacer = c1r(0).map((k) => ' ') + " | ";
        val horzSpacer = c1r(0).map((k) => '-') + "---" +
            prodr(0).map((k) => '-')

        for (i <- 0 until c2.rows) {
            print(spacer);
            println(c2r(i))
        }

        println(horzSpacer);
        for (i <- 0 until c1.rows) {
            print(c1r(i));
            print(" | ");
            println(prodr(i))
        }
        println();
        return c1 * c2;
    }

    def toDoubleMatrix(o : Cartan) = o.map(v=>v.toDouble);
    def toIntMatrix(o : linalg.DenseMatrix[Double]) = o.map(v=>math.round(v).toInt);


    def MatrixReduction(start: Cartan, goal: Cartan, basis: Array[Cartan], step: Int = 0): Unit = {
        var in = 0;
        val inputLoop = new Breaks;
        if (step == 0) println(start);
        inputLoop.breakable {
            while (true) {
                println(s"Iteration ${step}, Enter Next Step: ")
                in = StdIn.readInt() - 1;
                if (in == -2) {
                    return;
                }
                if (in >= 0 && in < basis.length) {
                    println(s"Input $in");
                    inputLoop.break;
                } else {
                    print(s"Input $in Invalid, Try Again ")
                }
            }
        }

        val stepChoice = basis(in);
        val res = printMatrixMult(stepChoice, start);
        if (res == goal) return;
        return MatrixReduction(res, goal, basis, step + 1);
    }
    type MatrixChain = (Chain, Cartan);
    implicit def MatrixChain2Matrix(p: MatrixChain) = p._2;

    def printLabel(s : Any, label : String = "") = {
        if(label != "") println(label);
        println(s)
        println();
    }


    def main(): Unit = {

        implicit val dim = 4;
        val rootSystem = RootSystems('F');

        //  Conjecture: G3+ is infinite? F5+, E9+ also infinite?
        // Trying to generate the G3 matrices will give you a group with infinite order?

        val rangle = Array.range(0, dim).map((k) => s"a_$k")
        implicit val ring = MultivariateRing(Q, rangle);

        implicit val c: Cartan = CartanMatrix(dim, rootSystem)
        val cInv = linalg.inv(c) //.map(v => math.round(v.floatValue()));

        val id = (x: ring.PolyType) => x
        val mId = linalg.DenseMatrix.eye[Int](dim);
        val revDiag = linalg.DenseMatrix
            .eye[Int](dim)
            .mapPairs((p, v) => if (p._1 + p._2 == dim - 1) 1 else 0);
        // println(revDiag);
        // println(linalg.inv(revDiag))
        val sqrt2 = math.sqrt(2);

        val ff = linalg.DenseMatrix(
          (sqrt2 / 2, 0.0, 0.0, 0.0),
          (0.0, sqrt2 / 2, 0.0, 0.0),
          (0.0, 0.0, sqrt2, 0.0),
          (0.0, 0.0, 0.0, sqrt2)
        );

        println(ff);
        val cD = toDoubleMatrix(c);
        val ffI = linalg.inv(ff)
        println(ff*cD *ffI);

        def flippy(w : Cartan) = toIntMatrix(ff*toDoubleMatrix(w)*ffI);

        val x_ = ring.generators
        val a_ = reflectionRoots(c)
        val s = reflections(a_)
        val y_ = x_.mapWithIndex((x, i) => s(i)(x))

        val D = s.mapWithIndex((refl, index) => Differential(a_)(ring)(refl, index));

        val sM = genReflectionMatrixs(c);

        // Column vector representations of `x_i`
        val xV = Array.tabulate(dim)(ColVector(dim));

        // The Monomial that gets reduced to one - would be the last element of the chain ^ of the chain len
        def ChainMono(ch: Chain) = (x_(ch.last) ^ (ch.length));
        def ChainPartial(ch: Chain) = ch.map(D);
        def ChainMatrix(ch: Chain) = if (ch.isEmpty) mId else ch.map(sM).reduce((a, b) => a * b);
        def invM(k: MatrixChain) = (k._1.reverse, ChainMatrix((k._1.reverse)));

        // def

        // def inverseM : Op[MatrixChain] = (c) =>
        // Maximal chains in F4.
        // var chains = Array[Chain](
        //   Array(1, 0),
        //   Array(1),
        //   Array(2, 1, 2),
        //   Array(3, 2, 1, 2, 3)
        // );
        // var monos = chains.map(ChainMono)
        // var partialChains = chains.map(ChainPartial);

        // Matrix representation of reflections in `x_i`.

        // Weyl Group matrix representation
        val wM = genWeylGroupMatrixs(dim, sM, 1500);

        // println(wM.length);
        // printMatrixMult(sM(1), wM(100)._2);
        val target = 293;
        // println(wM(target)._1.length);
        // printMatrixMult(
        //   sM(2),
        //   wM(target)
        // )

        // println(c * xV(0))
        // println(sM(0)*c*xV(0));
        // println(invM(wM(target))*c*xV(0));
        // println(wM(target))

        // println(c*xV(1  ));
        // printlnArray(sM);
        // MatrixReduction(sM(1), mId, sM);

// Conjecture - the ith row in [w] is also equal to the ith column in [w]^-1 in \alpha basis
// ok
// if [wx]^T = [wa]^-1 then chilling

        val rM = wM(target);
        val rMInv = invM(rM);
        val rMInv_a = (cInv * (rMInv * c).map(v => v.toDouble)).map(v => math.round(v).toInt)

        printLabel(sM(1), "rM");
        printLabel(flippy(sM(1)), "rM Flippy");
        // // println(cInv);
        // println();

        // println(rMInv_a)

        // println()
        // println("[w]^T - [w^-1]_a:")
        // println(rM._2.t - rMInv_a)
        // println(s(1)(              ));

        // Checks that in all matrixes of the Weyl Representation,
        // each row is either positive or negative semidefinite.
        // There are no rows that contain both positive and negative numbers.

        // Checked for An, Bn, Cn, Dn, F4, G2 | n <= 4.

        // Also checked for G3, E6, F5 |W| <= 1500
        def checkSemiDefinite(m: Cartan): Boolean = {
            for (row <- m.rowRepr) {
                var numRep = 0;
                for (j <- row.t) {
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
        // val res = polytopia.TestUtils.runTests(wM, (k: (Chain, Cartan)) => checkSemiDefinite(k._2));
        // println("passed: " + res.status + " num tested: " + res.numTested)
    }

}
