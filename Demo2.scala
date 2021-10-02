import stainless.equations._
import stainless.annotation._

object Demo2 {

    sealed abstract class List[T] {
        def isEmpty[T]: Boolean = this match {
            case Nil() => true
            case _ => false
        }

        def ::(x: T): List[T] = Cons(x, this)
    
        def ++(l: List[T]): List[T] = this match {
            case Nil() => l
            case Cons(x, xs) => x :: (xs ++ l) // Cons(x, (xs ++ l))
        }

        def head: T = {
            require(!isEmpty)
            val Cons(x, xs) = this
            x
        }

        def tail: List[T] = {
            require(!isEmpty)
            val Cons(x, xs) = this
            xs
        }
    }


    case class Nil[T]() extends List[T]
    case class Cons[T](head: T, tail: List[T]) extends List[T]


    def test[T](l: List[T], x: T): Unit = {
        assert(Nil() ++ l == l)
        assert(x :: Nil() ++ l == x :: l)
        
        appendNil(l)
        // assert(l ++ Nil() == l)
        // appendNil2(l)
        assert(l ++ Nil() == l)
    }

    def appendNil[T](l: List[T]): Unit = {

        if (!l.isEmpty) {

        }
        // if (!l.isEmpty) {
        //     // assert(l ++ Nil() == l.head :: (l.tail ++ Nil()))

        //     // // induction hypothesis (IH): append(l.tail, nil) = l.tail
        //     // appendNil(l.tail)
        //     // assert(l.head :: l.tail ++ Nil() == l.head :: l.tail)

            
        //     // assert(l.head :: l.tail == Cons(l.head, l.tail))
        //     // assert(Cons(l.head, l.tail) == l)

        //     (
        //         l ++ Nil()                          ==:| trivial |:
        //         (l.head :: (l.tail ++ Nil()))       ==:| appendNil(l.tail) |:
        //         (l.head :: l.tail)                  ==:| trivial |:
        //         l
        //     ).qed
        // }

    }.ensuring( _ => l ++ Nil() == l )


    def appendNil2[T](@induct l: List[T]): Unit = {
        ()
    } .ensuring(_ => l ++ Nil() == l)

}