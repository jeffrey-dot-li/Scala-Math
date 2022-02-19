package polytopia

import scala.reflect.ClassTag
import scala.collection.mutable.ArrayBuffer

class TestRes[A](implicit ct: ClassTag[A]) {
    var numTested = 0;
    def numFailed = errors.length;
    def numPassed = numTested - numFailed;

    var errors = ArrayBuffer[A]();
    def status = errors.isEmpty;
    def pass(a: A) {
        numTested += 1;
    }
    def fail(a: A) {
        numTested += 1;
        errors.addOne(a);
    }
};

case class TestDescrip();

object TestUtils {

    def runTests[A](zoo: Array[A], predicate: (A) => Boolean)(implicit ct: ClassTag[A])
        : TestRes[A] = {
        var res = new TestRes[A]()

        for (sub <- zoo) {
            val testRes = predicate(sub);
            if (testRes) {
                res.pass(sub)
            } else {
                res.fail(sub);
            }
        }

        return res;
    }
}
