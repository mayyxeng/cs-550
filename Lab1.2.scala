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

  

  def subListOfAppended[T](l1: List[T], l2: List[T], v: T): Unit = {
    require(subList(l1, l2) && !l2.isEmpty)
    if (l1.isEmpty) {
        // trivial 
        (
            subList(l1, Cons(v, l2))   ==:| trivial |:
            subList(Nil(), Cons(v, l2)) ==:| trivial |:
            true
        ).qed
    } else {
        assert(!l2.isEmpty)
        
        // (
        //         subList(l1, Cons(v, l2))                                ==:| trivial |:
        //         ((l1 == v && subList(l1.tail, l2)) || subList(l1, l2))  ==:| trivial |: 
        //         true
        // ).qed
    }
    
  } .ensuring {_ =>
      subList(l1, Cons(v, l2))
  }

  def subListTail[T](l1 : List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && subList(l1, l2))

    assert(!l2.isEmpty)

    (l1, l2) match {
        case (Nil(), _) => // impossible
        case (_, Nil()) => // also imposible
        case (Cons(_, _), Cons(_, _)) =>
            if (subList(l1, l2.tail)) {
                // induction precondition on l2 holds because we have constained
                // the case with the if
                // subListTail(l1, l2.tail) // use the induction hypothesis
                // which implies that subList(l1.tail, l2.tail)
                // assert(subList(l1.tail, l2.tail))
                // now we need to prove that subList(l1.tail, l2.tail)
                // implies that subList(l1.tail, any_x :: l2.tail)
                // which implies that subList(l1.tail, l2.head :: l2.tail)
                // i.e., subList(l1.tail, l2)
                // subListOfAppended(l1.tail, l2.tail, l2.head)
                // assert(subList(l1.tail, l2.head :: l2.tail))
                // all can be summarized as (note that without the subListOfAppended lemma.
                // the proof still works, because stainless can understand it)  
                subListTail(l1, l2.tail)
                ()
            } else {
                // induction precondition does not hold, however we know that
                // subList(l1, l2) = ((l1.head === l2.head) && subList(l1.tail, l2.tail)) || subList(l1, l2.tail)
                // but since subList(l1, l2.tail) == false, then 
                // we have 
                assert((l1.head == l2.head) && subList(l1.tail, l2.tail))
                // so we have 
                assert(subList(l1.tail, l2.tail))
                // and by the subListOfAppended
                assert(subList(l1.tail, l2.head :: l2.tail))
                ()
            }
        
    }

  }.ensuring(_ => 
      subList(l1.tail, l2)
  )
  

 
  def subListTails[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && !l2.isEmpty && l1.head == l2.head && subList(l1, l2))
    // directly driven from the previous one
    (l1, l2) match {
            case (Cons(_, _), Cons(_, _)) =>
                if (subList(l1, l2.tail)) {
                    // we know that !l1.isEmpty and subList(l1, l2.tail), so 
                    // the preconditions for subListTail(l1, l2.tail) hold
                    subListTail(l1, l2.tail)
                    // by subListTail(l1, l2.tail) now we know 
                    // subList(l1.tail, l2.tail) which is the proven immediately
                    ()
                } else {
                    // since subList(l1, l2) holds and subList(l1, l2.tail)
                    // does not hold, we know that (l1.head == l2.head) &&
                    // subList(l1.tail, l2.tail) should hold,
                    // we already know that l1.head == l2.head by the preconditions
                    // so 
                    assert(subList(l1.tail, l2.tail))
                    // in fact, this shows that the precondition l1.head == l2.head
                    // is not really needed
                    // is also know, i.e., proven            
                    ()
                }
        }
    
  }.ensuring(_ =>
    subList(l1.tail, l2.tail)
  )

  def subListTailsRelaxed[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && !l2.isEmpty && subList(l1, l2))
    // directly driven from the previous one
    (l1, l2) match {
            case (Cons(_, _), Cons(_, _)) =>
                if (subList(l1, l2.tail)) {
                    subListTail(l1, l2.tail)
                    ()
                } else {
                    ()
                }
        }
    
  }.ensuring(_ =>
    subList(l1.tail, l2.tail)
  )

//   def lemma[T](ll1: List[T], ll2: List[T], vv: T): Unit = {
//     require(subList(ll1, ll2))
//   }.ensuring (_ =>
//     subList(vv :: ll1, vv :: ll2)
//   )
  
  def subListTrans[T](l1: List[T], l2: List[T], l3: List[T]): Unit = {
    require(subList(l1, l2) && subList(l2, l3))

    
    (l1, l2, l3) match {
        case (Nil(), _, _) =>
            ()
        case (Cons(x, xs), Cons(y, ys), Cons(z, zs)) =>
            // we do induction on l3, i.e., we have 
            // subList(l1, l2) and subList(l2, zs) implies that
            // subList(l1, zs)
            // furthermore
            // subList(l1, l2) then either
            val cond_A = (x == y) && subList(xs, ys)
            val cond_B = subList(Cons(x, xs), ys)
            // holds
            // similarly
            // subList(l2, l3) then either
            val cond_C = (y == z) && subList(ys, zs)
            val cond_D = subList(Cons(y, ys), zs)
            // holds, so we have the following combinations
            if (cond_A && cond_C) {
                // we know that subList(xs, ys) is true, and subList(ys, zs)
                // is also true and also x == y == z, 
                // by induction subList(xs, zs) is also true
                subListTrans(xs, ys, zs)
                assert(subList(xs, zs))
                assert(subList(x::xs, z::zs))
                // proven
                ()
            } else if (cond_A && cond_D) {
                // we know from cond_A that subList(xs, ys) is true and 
                // from cond_D that subList(Cons(y, ys), zs) is also true
                // however, since x == y the we can say subList(x :: xs, y :: ys)
                // is true, now all we need to to do is to apply the induction
                // hypothesis and then that gives us subList(x :: xs, zs)
                // which trivially says that subList(x :: xs, z :: zs), i.e.,
                // proved the hypothesis
            
                assert(subList(x :: xs, y :: ys))
                subListTrans(x::xs, y::ys, zs)
                
                ()
            } else if (cond_B && cond_C) {
                // we know that subList(x :: xs, ys), and so we have 
                // subList(ys, zs) are true, but by induction we know
                // subList(x :: xs, zs) should also be true, which means
                // sublist(x :: xs, z :: zs) is also true
                subListTrans(x :: xs, ys, zs)
                ()
            } else if (cond_B && cond_D) {
                // subList(x::xs, ys) is valid, so is subList(y::ys, zs)
                // by the assumption, but we can also say that 
                // subList(ys, zs) is valid by subListTail lemma
                subListTail(y :: ys, zs)
                // so by induction 
                subListTrans(x :: xs, ys, zs)
                // we have subList(x :: xs, zs) and trivial subList(x :: xs, z :: zs)
                ()
            }
            
    }
 
  }.ensuring(_ =>
    subList(l1, l3)
  )

  def subListLength[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2))
    
    (l1, l2) match {
        case (Nil(), _) =>
            () 
        case (Cons(x, xs), Cons(y, ys)) =>
            // by lemma subLisTailsRelaxed
            // subList(x :: xs, y :: ys) implies that subList(xs, ys)
            subListTailsRelaxed(x :: xs, y :: ys)
            assert(subList(xs, ys))
            // so the preconditions for the induction is valid and this 
            subListLength(xs, ys)
            // tells us xs.length <= ys.length
            // which trivial says (x :: xs).length <= (y :: ys).length, i.e.,
            // proved the hypothesis
            ()
    }
 
  }.ensuring(_ =>
    l1.length <= l2.length
  )

  def notSubListIfGreaterLength[T](ll1: List[T], ll2: List[T]): Unit = {
        require(ll1.length > ll2.length)
        (ll1, ll2) match {
            case (Nil(), _) =>
                ()
            case (_, Nil()) =>
                ()
            case (Cons(_, _), Cons(_, _)) =>
                notSubListIfGreaterLength(ll1, ll2.tail)
                // we know ll1 cannot be subList of ll2.tail but induction
                assert(!subList(ll1, ll2.tail))
                // also by induction, ll1.tail can not be a subList of ll2.tail
                notSubListIfGreaterLength(ll1.tail, ll2.tail)
                assert(!subList(ll1.tail, ll2.tail))
        }
    }.ensuring(_ =>
        !subList(ll1, ll2)
    )
  def subListEqual[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2) && l1.length >= l2.length)

    (l1, l2) match {
        case (Nil(), _) => 
            () 
        case (Cons(x, xs), Cons(y, ys)) =>
            // subList(l1, l2) holds then by the subListLength lemma
            // we know that l1.length <= l2.length
            subListLength(l1, l2)
            assert(l1.length <= l2.length)
            // we also know (assumption) that l1.length >= l2.length
            // so l1.length == l2.length
            assert(l1.length == l2.length)
            subListTailsRelaxed(x :: xs, y :: ys)
            // by lemma subListTailsRelaxed, we know subList(xs, ys) is true
            assert(subList(xs, ys))
            // now if use the induction, we can say xs == ys, but this does not
            // tells use that x :: xs == y :: ys, i.e., we need to prove that
            // x == y too
            subListEqual(xs, ys)
            // this can be done by noting that x :: xs has larger length than
            // ys, so subList(x :: xs, ys) should be false, but 
            // subList(x :: xs, y :: ys) and subList(xs, ys) are also true
            // then by the definition of subList
            // subList(x :: xs, y :: ys) = (x == y && subList(xs, ys)) || subList(x :: xs, ys)
            // if subList(x :: xs, ys) is flase then we have x == y
            notSubListIfGreaterLength(x :: xs, ys) 
            assert(x == y)
            // the rest is trivial, xs == ys && x == y then l1 == l2          
            
    }
 
  }.ensuring(_ =>
    l1 == l2
  )

  def subListAntisym[T](l1: List[T], l2: List[T]): Unit = {
    require(subList(l1, l2) && subList(l2, l1))

    
    
    subListLength(l2, l1)
    // impliest that l1.length >= l2.length
    // but also subList(l1, l2)
    // so we have from subListEqual(l1, l2) that l1 == l2
    subListEqual(l1, l2)
 
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