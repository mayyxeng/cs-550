import stainless.annotation._

object Demo {

    def f(x: BigInt, y: BigInt): BigInt = {
        require(x >= 0 && y >= 1)
        x * y
    } .ensuring { res =>
        res >= x
    }

    def g(z: BigInt): Unit = {
        require(z >= 1)
        val r1 = f(z, z)
        val r2 = f(2, 1)
        val r3 = f(4, 10)

        assert(r3 >= 10)
        assert(r2 == 2)
    }

    // @extern
    def main(args: Array[String]): Unit = {
        println(args.reduce(_ + _))
    }
}