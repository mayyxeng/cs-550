import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.equations._


object SubList {
 
  def subList[T](l1: List[T], l2: List[T]): Boolean = (l1, l2) match {
    case (Nil(), _)                 => true
    case (_, Nil())                 => false
    case (Cons(x, xs), Cons(y, ys)) => (x == y && subList(xs, ys)) || subList(l1, ys)
  }
 
  def subListRefl[T](l: List[T]): Unit = {
    
    l match {
        case Nil() =>
            ()
        case Cons(x, xs) =>
            (
                subList(l, l)                                       ==:| trivial |:
                ((x == x && subList(xs, xs)) ||  subList(l, xs))    ==:| subListRefl(xs) |:
                true
                
            ).qed
    }
  }.ensuring(_ =>
    subList(l, l)
  )

  def subListTail[T](l1: List[T], l2: List[T]): Unit = {
      require(!l1.isEmpty && subList(l1, l2))
      (l1, l2) match {
          case (Cons(x, xs), Cons(y, ys)) =>
              if (subList(l1, ys)) {
                  subListTail(l1, ys)
                  ()
              } else {            
                  ()
              }
      }
  }.ensuring(_ =>
      subList(l1.tail, l2)
  )  
    
  def subListTails[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && !l2.isEmpty && l1.head == l2.head && subList(l1, l2))

    (l1, l2) match {
            case (Cons(x, xs), Cons(y, ys)) =>
                if (subList(l1, ys)) {
                    subListTail(l1, ys)
                    ()
                } else {            
                    ()
                }
        }
    
  }.ensuring(_ =>
    subList(l1.tail, l2.tail)
  )

  def subListTailsGeneral[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && !l2.isEmpty && subList(l1, l2))

    (l1, l2) match {
            case (Cons(x, xs), Cons(y, ys)) =>
                if (subList(l1, ys)) {
                    subListTail(l1, ys)
                    ()
                } else {            
                    ()
                }
        }
    
  }.ensuring(_ =>
    subList(l1.tail, l2.tail)
  )

  def subListTrans[T](l1: List[T], l2: List[T], l3: List[T]): Unit = {
    require(subList(l1, l2) && subList(l2, l3))

    
    (l1, l2, l3) match {
        case (Nil(), _, _) =>
            ()
        case (Cons(x, xs), Cons(y, ys), Cons(z, zs)) =>
            subListTailsGeneral(l1,l2)
            subListTailsGeneral(l2,l3)
            subListTrans(l1.tail, l2.tail, l3.tail)
            assert(subList(l1.tail, l3.tail))

            if (subList(l1, l2.tail)) {
                subListTrans(l1,l2.tail,l3.tail)
            } else {
                assert(l1.head == l2.head)
                if (subList(l2, l3.tail)) {
                    subListTrans(l1,l2,l3.tail)
                } else {
                    
                }
            } 
    }
 
  }.ensuring(_ =>
    subList(l1, l3)
  )
 
 
  def subListLength[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2))

    l1 match {
        case (Nil()) =>
            ()
        case (Cons(x,xs)) =>
            subListTailsGeneral(l1,l2)
            subListLength(l1.tail, l2.tail)
    }
 
  }.ensuring(_ =>
    l1.length <= l2.length
  )

  def subListPrecond[T](l1: List[T], l2: List[T]): Unit = {
    require(l1.length > l2.length)

    l2 match {
      case (Nil()) => 
        ()
      case (Cons(y,ys)) =>
        subListPrecond(l1,ys)
        subListPrecond(l1.tail,ys)
    }

  }.ensuring(_ =>
    !subList(l1,l2)
  )
 
  def subListEqual[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2) && l1.length >= l2.length)

    subListLength(l1,l2)
    assert(l1.length == l2.length)
    l1 match {
        case (Nil()) => 
            ()
        case (Cons(x,xs)) =>
            subListTailsGeneral(l1, l2)
            subListPrecond(l1,l2.tail)
            assert(l1.head == l2.head)
            subListEqual(l1.tail,l2.tail)
    }
 
  }.ensuring(_ =>
    l1 == l2
  )
 
  def subListAntisym[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2) && subList(l2, l1))

    subListLength(l2,l1)
    subListEqual(l1,l2)

  }.ensuring(_ =>
    l1 == l2
  )
 
  @extern
  def main(args: Array[String]): Unit = {
    println(subList(List(0, 2), List(0, 1, 2))) // true
    println(subList(List(1, 0), List(0, 0, 1))) // false
    println(subList(List(10, 5, 25), List(70, 10, 11, 8, 5, 25, 22))) // true
  }
 
}