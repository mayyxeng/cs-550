
import stainless.annotation._
import stainless.collection._
import stainless.annotation._
import stainless.equations._

object Demo3 {


    sealed abstract class Tree {

        def isSearchTree: Boolean = this match {
            case Leaf => true
            case Node(root, left, right) => 
                left.isSearchTree && 
                right.isSearchTree &&
                left.forall(_ <= root) &&
                right.forall(_ >= root)
        }

        def forall(p: BigInt => Boolean): Boolean = this match {
            case Leaf => true
            case Node(root, left, right) => p(root) &&
                left.forall(p) && right.forall(p)
        }

        def insert(n: BigInt): Tree = this match {
            case Leaf => Node(n, Leaf, Leaf)
            case Node(root, left, right) if n <= root =>
                Node(root, left.insert(n), right)
            case Node(root, left, right) =>
                Node(root, left, right.insert(n))
        }

        def toList: List[BigInt] = this match {
            case Leaf => Nil()
            case Node(root, left, right) => left.toList ++ (root :: right.toList)
        }

    }

    case object Leaf extends Tree
    case class Node(root: BigInt, left: Tree, right: Tree) extends Tree


    def insert(ls: List[BigInt], n: BigInt): List[BigInt] = ls match {
        case Nil() => n :: Nil()
        case Cons(x, xs) if n <= x => n :: ls
        case Cons(x, xs) => x :: insert(xs, n)
    }



    def insertAppendLeft(
         l1: List[BigInt], l2: List[BigInt], middle: BigInt, n: BigInt
    ): Unit = {
        require(n <= middle)

        l1 match {
            case Nil() =>
                (
                    insert(l1 ++ (middle :: l2), n)          ==:| trivial |:
                    insert(Nil() ++ (middle :: l2), n)       ==:| trivial |:
                    insert(middle :: l2, n)                  ==:| trivial |:
                    n :: (middle :: l2)                      ==:| trivial |:
                    (n :: Nil()) ++ (middle :: l2)           ==:| trivial |:
                    insert(Nil(), n) ++ (middle :: l2)       ==:| trivial |:
                    insert(l1, n) ++ (middle :: l2)          
                ).qed
            case Cons(x1, xs1) if n <= x1 =>
                (
                    insert((x1 :: xs1) ++ (middle :: l2), n)         ==:| trivial |:
                    n :: ((x1 :: xs1) ++ (middle :: l2))             ==:| trivial |:
                    (n :: Nil()) ++ (l1 ++ (middle :: l2))           ==:| trivial |:
                    (n :: Nil()) ++ l1 ++ (middle :: l2)             ==:| trivial |:
                    (n :: l1) ++ (middle :: l2)                      ==:| trivial |:
                    insert(l1, n) ++ (middle :: l2)         
                ).qed
            case Cons(x1, xs1) => // n > x1
                (
                    insert(l1 ++ (middle :: l2), n)                  ==:| trivial |:
                    insert((x1 :: xs1) ++ (middle :: l2), n)         ==:| trivial |:
                    x1 :: insert(xs1 ++ (middle :: l2), n)           ==:| insertAppendLeft(xs1, l2, middle, n)  |:
                    x1 :: (insert(xs1, n) ++ (middle :: l2))         ==:| trivial |:
                    insert(l1, n) ++ (middle :: l2)
                ).qed
        }
       
    } .ensuring {_ =>
        insert(l1 ++ (middle :: l2), n) == insert(l1, n) ++ (middle :: l2)
    }

    def insertAppendRight(@induct l1: List[BigInt], l2: List[BigInt], middle: BigInt, n: BigInt): Unit = {
        require(l1.forall(_ < n) && middle < n)
    }.ensuring(_ =>
        insert(l1 ++ (middle :: l2), n) == l1 ++ (middle :: insert(l2, n))
    )


    
    def forallToList(t: Tree, p: BigInt => Boolean): Unit = {
        require(t.forall(p))

        t match {
            case Leaf =>
                ()
            case Node(root, left, right) =>
                forallToList(left, p)
                // assert(left.toList.forall(p))
                forallToList(right, p)
                // assert(right.toList.forall(p))

                ListSpecs.listAppendValidProp(root :: right.toList, left.toList, p)
                // assert((left.toList ++ (root :: right.toList)).forall(p))
                // assert(t.toList.forall(p))
        }
    }.ensuring {
        t.toList.forall(p)
    }

    def strictUpperBound(
        @induct l: List[BigInt], x1: BigInt, x2: BigInt
    ): Unit = {
        require(l.forall(_ <= x1) && x1 < x2)

    }.ensuring{ _ =>
        l.forall(_ < x2)
    }

    def insertTreeList(t: Tree, n: BigInt): Unit = {
        require(t.isSearchTree)

        t match {
            case Leaf => 
                ()
            case Node(root, left, right) if n <= root =>
                (
                    t.insert(n).toList                                  ==:| trivial |:
                    Node(root, left.insert(n), right).toList            ==:| trivial |:
                    left.insert(n).toList ++ (root :: right.toList)     ==:| insertTreeList(left, n) |:
                    insert(left.toList, n) ++ (root :: right.toList)    ==:| insertAppendLeft(left.toList, right.toList, root, n) |:
                    insert(left.toList ++ (root :: right.toList), n)    ==:| trivial |:
                    insert(t.toList, n)
                ).qed
            case Node(root, left, right) =>
                assert(left.forall(_ <= root))
                // assert(root < n)

                forallToList(left, _ <= root)
                // assert(left.toList.forall(_ <= root))
                strictUpperBound(left.toList, root, n)
                // assert(left.toList.forall(_ < n))

                (
                    t.insert(n).toList                                      ==:| trivial |:
                    Node(root, left, right.insert(n)).toList                ==:| trivial |:
                    left.toList ++ (root :: right.insert(n).toList)         ==:| insertTreeList(right, n) |:
                    left.toList ++ (root :: insert(right.toList, n))        ==:| insertAppendRight(left.toList, right.toList, root, n) |:
                    insert(left.toList ++ (root :: right.toList), n)        ==:| trivial |:
                    insert(t.toList, n)
                ).qed
                
        }
    }.ensuring{ _ =>
        t.insert(n).toList == insert(t.toList, n)
    }
}