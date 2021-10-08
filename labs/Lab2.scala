import stainless.lang._

object Lab02 {

  // -------- Part 1 -------------
  def search(arr: Array[Int], x: Int, lo: Int, hi: Int): Boolean = {
    
    require(hi < arr.length)
    require(lo >= 0)
    require(hi >= 0)
    
    decreases(if (lo < hi) (hi - lo) else 0) 
    if (lo < hi) {
      if (x == arr(hi) || x == arr(lo)) true // checks the boundaries
      else { // if not found in the boundaries
        val i: Int = (hi - lo) / 2 + lo // (hi + lo) / 2 can cause overflow
        val y = arr(i)
        if (i == 0 || i == arr.length - 1) false 
        else if (x == y) true
        else if (x < y) {
            search(arr, x, lo, i - 1)
        } else  {
            // assert((i + 1) >= 0 && (i + 1) < arr.length)
            search(arr, x, i + 1, hi)   
        }
      }
    } else if (lo == hi) {
      x == arr(lo)
    } else {
      false
    }
  }
    // -------- Part 1 -------------
//   def search(arr: Array[Int], x: Int, lo: Int, hi: Int): Boolean = {
    
//     require(lo >= 0)
//     require(hi >= 0)
//     // require(lo < arr.length)
//     require(hi < arr.length)
//     // require(hi > lo + 1)
//     require( if (hi < lo) (lo - hi) >= 2 else (hi - lo) >= 2)
//     decreases(-1) // Find the correct mesure
//     if (lo <= hi) {
//       val i = {
//           if (lo == hi)
//         (hi - lo) / 2 + lo

//       }
//       val y = arr(i)
//       if (x == y) true
//       else if (x < y) search(arr, x, lo, i - 1)
//       else search(arr, x, i + 1, hi)
//     } else {
//       false
//     }
//   }

  // -------- Part 2 -------------



  sealed abstract class Tree[T]

  case class Leaf[T]() extends Tree[T]

  case class Node[T](root: T, left: Tree[T], right: Tree[T]) extends Tree[T]

  def forall[T](t: Tree[T], p: T => Boolean): Boolean = {
    decreases(t)
    t match {
      case Leaf() => true
      case Node(root, left, right) => p(root) && forall(left, p) && forall(right, p)
    }
  }

  def isOrdered(t: Tree[BigInt]): Boolean = {
    decreases(t)
    t match {
      case Leaf() => true
      case Node(root, left, right) =>
        forall(left, (node: BigInt) => node <= root) &&
          forall(right, (node: BigInt) => node >= root) &&
          isOrdered(left) &&
          isOrdered(right)
    }
  }

  def insert(t: Tree[BigInt], x: BigInt): Tree[BigInt] = {
    require(isOrdered((t)))
    t match {
      case Leaf() => Node(x, Leaf(), Leaf())
      case Node(root, left, right) if (root > x) => Node(root, insert(left, x), right)
      case Node(root, left, right) if (x > root) => Node(root, left, insert(right, x))
      case _ => t // case where root == x
    }
  }

  def forallAfterInsert(t: Tree[BigInt], x: BigInt, p: BigInt => Boolean): Unit = {
    require(isOrdered(t) && forall(t, p) && p(x))
    t match {
      case Leaf() => ()
      case Node(root, left, right) if (root > x) => forallAfterInsert(left, x, p)
      case Node(root, left, right) if (x > root) => forallAfterInsert(right, x, p)
      case _ => ()
    }
  } ensuring (_ => forall(insert(t, x), p))

  
  def orderedAfterInsert(t: Tree[BigInt], x: BigInt): Unit = {
    require(isOrdered(t))
    t match {
      case Leaf() => ()
      case Node(root, left, right) if (root > x) =>
    
        forallAfterInsert(left, x, n => n <= root)
        orderedAfterInsert(left,  x)
        
      case Node(root, left, right) if (x > root) =>
        
        forallAfterInsert(right, x, n => n >= root)
        orderedAfterInsert(right,  x)
        
      case _ => ()
    }
  } ensuring (_ => isOrdered(insert(t, x)))

}
