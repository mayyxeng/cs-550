import java.text.Normalizer.Form
object Lab04 {

  // Term syntax
  sealed abstract class Term
  case class Var(name: String) extends Term
  case class Function(name: String, children: List[Term]) extends Term

  //Formula syntax
  sealed abstract class Formula
  case class Predicate(name: String, children: List[Term]) extends Formula

  case class And(children: List[Formula]) extends Formula
  case class Or(children: List[Formula]) extends Formula
  case class Implies(left: Formula, right: Formula) extends Formula
  case class Neg(inner: Formula) extends Formula

  case class Forall(variable: String, inner: Formula) extends Formula
  case class Exists(variable: String, inner: Formula) extends Formula

  def printTree(f: Formula)(indent: Int = 0): Unit = {
    val indent_str = " " * indent
    f match {
      case Predicate(name, children) =>
        println(s"${indent_str}${f} ")
      case And(children) =>
        println(s"${indent_str}And(")
        children.foreach { c =>
          printTree(c)(indent + 2)
        }
        println(s"${indent_str})")
      case Or(children) =>
        println(s"${indent_str}Or(")
        children.foreach { c =>
          printTree(c)(indent + 2)
        }
        println(s"${indent_str})")
      case Implies(left, right) =>
        printTree(left)(indent + 2)
        println(s"${indent_str}implies ")
        printTree(right)(indent + 2)
      case Neg(inner) =>
        println(s"${indent_str}Not(")
        printTree(inner)(indent + 2)
        println(s"${indent_str})")
      case Forall(variable, inner) =>
        println(s"${indent_str}Forall.${variable}(")
        printTree(inner)(indent + 2)
        println(s"${indent_str})")
      case Exists(variable, inner) =>
        println(s"${indent_str}Exists.${variable}(")
        printTree(inner)(indent + 2)
        println(s"${indent_str})")
    }

  }
  /*
    Computes the free variables of a Term, respectively a Formula.
   */
  def freeVariables(t: Term): Set[Var] = t match {
    case v: Var                   => Set(v)
    case Function(name, children) => children.flatMap(freeVariables).toSet
  }
  def freeVariables(f: Formula): Set[Var] = f match {
    case Predicate(name, children) => children.flatMap(freeVariables).toSet
    case And(children)             => children.flatMap(freeVariables).toSet
    case Or(children)              => children.flatMap(freeVariables).toSet
    case Implies(left, right)    => freeVariables(left) ++ freeVariables(right)
    case Neg(inner)              => freeVariables(inner)
    case Forall(variable, inner) => freeVariables(inner) - Var(variable)
    case Exists(variable, inner) => freeVariables(inner) - Var(variable)
  }

  /*
    Performs simultaneous substitution of Vars by Terms
   */
  def substitute(t: Term, subst: Map[Var, Term]): Term = t match {
    case v: Var => subst.getOrElse(v, v)
    case Function(name, children) =>
      Function(name, children.map(substitute(_, subst)))
  }

  def substitute(f: Formula, subst: Map[Var, Term]): Formula = f match {
    case Predicate(name, children) =>
      Predicate(name, children.map(substitute(_, subst)))
    case And(children) => And(children.map(substitute(_, subst)))
    case Or(children)  => Or(children.map(substitute(_, subst)))
    case Implies(left, right) =>
      Implies(substitute(left, subst), substitute(right, subst))
    case Neg(inner)       => Neg(substitute(inner, subst))
    case Forall(v, inner) => Forall(v, substitute(inner, subst))
    case Exists(v, inner) => Exists(v, substitute(inner, subst))
  }
  //We don't need substitution in Formulas, which conveniently avoid having to implement capture avoiding substitution.

  /*
    Make sure that all bound variables are uniquely named, and with names different from free variables.
    This will simplify a lot future transformations. The specific renaming can be arbitrary
   */
  def makeVariableNamesUnique(f: Formula): Formula = {
    var i: Int = 0
    def mVNUForm(f: Formula, subst: Map[Var, Var]): Formula = {
      f match {
        case Predicate(name, children) =>
          Predicate(name, children.map(t => substitute(t, subst)))
        case And(children) => And(children.map(s => mVNUForm(s, subst)))
        case Or(children)  => Or(children.map(s => mVNUForm(s, subst)))
        case Implies(left, right) =>
          Implies(mVNUForm(left, subst), mVNUForm(right, subst))
        case Neg(inner) => Neg(mVNUForm(inner, subst))
        case Forall(variable, inner) =>
          val nvar = "x" + i
          i += 1
          val t = mVNUForm(inner, subst + ((Var(variable), Var(nvar))))
          Forall(nvar, t)
        case Exists(variable, inner) =>
          val nvar = "x" + i
          i += 1
          val t = mVNUForm(inner, subst + ((Var(variable), Var(nvar))))
          Exists(nvar, t)
      }
    }
    val alreadyTaken =
      freeVariables(f).zipWithIndex.map(p => (p._1, Var("x" + p._2)))
    i = alreadyTaken.size
    mVNUForm(f, alreadyTaken.toMap)
  }

  /*
    Put the formula in negation normal form.
   */
  def negationNormalForm(f: Formula): Formula = {

    f match {
      case Neg(inner) =>
        // propagate negatation case by case
        inner match {
          case Neg(g) => negationNormalForm(g)
          case Implies(left, right) =>
            And(
              List(
                negationNormalForm(Neg(Neg(left))),
                negationNormalForm(Neg(right))
              )
            )
          case And(children) =>
            Or(children.map(x => negationNormalForm(Neg(x))))
          case Or(children) =>
            And(children.map(x => negationNormalForm(Neg(x))))
          case Predicate(_, _) => f
          case Exists(variable, inner) =>
            Exists(variable, negationNormalForm(Neg(inner)))
          case Forall(variable, inner) =>
            Forall(variable, negationNormalForm(Neg(inner)))
        }
      // do not propagate negation, since the current formula is not negates,
      // but make sure the final formula is of normal form by recursion
      case Implies(left, right) =>
        Or(List(negationNormalForm(Neg(left)), right))
      case And(children)   => And(children.map(negationNormalForm))
      case Or(children)    => Or(children.map(negationNormalForm))
      case Predicate(_, _) => f
      case Exists(variable, inner) =>
        Exists(variable, negationNormalForm(inner))
      case Forall(variable, inner) =>
        Forall(variable, negationNormalForm(inner))
    }
  }

  /*
    Put the formula in negation normal form and then eliminates existential quantifiers using Skolemization
   */

  def skolemizationNegation(f: Formula): Formula = {

    def skolemize(g: Formula): Formula = {
      g match {
        case Exists(variable, inner) =>
          // because `makeVariableNamesUnique is called before we get here, we
          // know that the variable name is unique already, so no need to create
          // new names..
          val fvs = freeVariables(g)
          // if (fvs.nonEmpty) {
          println(s"Free vars ${fvs} of tree")
          printTree(g)(4)
          println("END")
          skolemize(
            substitute(
              inner,
              Map(Var(variable) -> Function(variable, fvs.toList))
            )
          )
        // } else {
        //   // contant function, can keep the variable as is
        //   skolemize(inner)
        // }

        case Forall(variable, inner) => Forall(variable, skolemize(inner))
        case Or(children)            => Or(children.map(skolemize))
        case And(children)           => And(children.map(skolemize))
        case Neg(inner) =>
          Neg(skolemize(inner))
        case Predicate(name, children) => g
        case Implies(_, _) =>
          throw new RuntimeException(
            "Can only Skolemize NNF! Implication not allowed"
          )
      }
    }

    skolemize(makeVariableNamesUnique(negationNormalForm(f)))
  }

  /*
    Return the matrix of f in negation normal, skolemized form and make sure variables are uniquely named. Since there are no existential
    quantifiers and all variable names are unique, the matrix is equivalent to the whole formula.
   */
  def prenexSkolemizationNegation(f: Formula): Formula = {

    def transform(g: Formula): Formula = {
      g match {
        case Forall(variable, inner) => transform(inner)
        case And(children)           => And(children.map(transform))
        case Or(children)            => Or(children.map(transform))
        case Neg(inner)              => Neg(transform(inner))
        case Predicate(_, _)         => g
        case _ =>
          println("We fucked up")
          // printTree(g)(2)
          throw new RuntimeException(
            "prenex transform comes after Skoleminzation!"
          )
      }
    }

    transform(f)
  }

  type Clause = List[Formula]

  def printClause(clause: Clause): Unit = {

    println("{")
    clause.foreach { c => printTree(c)(3) }
    println("}")

  }
  /*
    This may exponentially blowup the size in the formula in general.
    If we only preserve satisfiability, we can avoid it by introducing fresh predicates, but that is not asked here.
   */
  def conjunctionPrenexSkolemizationNegation(f: Formula): List[Clause] = {
   
    def transformToBinOp(g: Formula): Formula = {
      g match {
        case Or(children) =>
          children match {
            case List(a, b) =>
              Or(List(transformToBinOp(a), transformToBinOp(b)))
            case a +: tail =>
              Or(List(transformToBinOp(a), transformToBinOp(Or(tail))))
          }
        case And(children) =>
          children match {
            case List(a, b) =>
              And(List(transformToBinOp(a), transformToBinOp(b)))
            case a +: tail =>
              And(List(transformToBinOp(a), transformToBinOp(And(tail))))
          }
        case _ => g
      }
    }

    def pushInOrs(g: Formula): Formula = {
      g match {
        case Or(List(a @ (Predicate(_, _) | Neg(_)), And(List(b, c)))) =>
          And(Or(List(a, b)) +: List(Or(List(a, c))))
        case Or(List(And(List(a, b)), c @ (Predicate(_, _) | Neg(_)))) =>
          // And(Or(List(a, c)), Or(List(b, c)))
          And(List(Or(List(a, c)), Or(List(b, c))))
        case Predicate(_, _) | Neg(_) => g
        case And(List(a, b))          => And(List(pushInOrs(a), pushInOrs(b)))
        case Or(List(a, b))           => Or(List(pushInOrs(a), pushInOrs(b)))
        case _ =>
          // printTree(g)(2)
          throw new RuntimeException("Fucked up")
      }
    }

    def fixedPoint(tree: Formula): Formula = {

      val transformed = pushInOrs(tree)

      def equalTrees(t: Formula, g: Formula): Boolean = {
        (t, g) match {
          case (Or(List(ta, tb)), Or(List(ga, gb))) =>
            equalTrees(ta, ga) && equalTrees(tb, gb)
          case (And(List(ta, tb)), And(List(ga, gb))) =>
            equalTrees(ta, ga) && equalTrees(tb, gb)
          case (Predicate(tv, ts), Predicate(gv, gs)) =>
            (tv == gv) && (ts == gs)
          case (Neg(ti), Neg(gi)) => equalTrees(ti, gi)
        }
      }

      if (equalTrees(tree, transformed)) {
        transformed
      } else {
        fixedPoint(transformed)
      }
    }
    println("Orignal tree")
    // printTree(f)(2)
    println("End orig")
    val bin_tree = transformToBinOp(f)
    println("Binary Op tree:")
    // printTree(bin_tree)(2)
    println("End of binary tree")
    val cnf = fixedPoint(bin_tree)
    def collectClauses(cnf: Formula)(clauses: List[Clause]): List[Clause] = {

      cnf match {
        case And(List(a, b)) =>
          collectClauses(b)(clauses ++ collectClauses(a)(clauses))
        case Predicate(_, _) | Neg(_) | Or(_) => List(cnf) +: clauses
      }

    }
    collectClauses(cnf)(List()).toSet.toList
  }
  /*
    A clause in a proof is either assumed, i.e. it is part of the initial formula, or it is deduced from previous clauses.
    A proof is written in a specific order, and a justification should not refer to a previous step.
   */
  sealed abstract class Justification
  case object Assumed extends Justification
  case class Deduced(premices: (Int, Int), subst: Map[Var, Term])
      extends Justification

  type ResolutionProof = List[(Clause, Justification)]

  /*
    Verify if a given proof is correct. The function should verify that every clause is correctly justified (unless assumed).

   */
  def checkResolutionProof(proof: ResolutionProof): Boolean = {
    ???
  }

  val a = Function("a", Nil)
  val b = Function("b", Nil)
  val c = Function("c", Nil)
  val x = Var("x")
  val y = Var("y")
  val z = Var("z")
  def lives(a: Term) = Predicate("lives", List(a))
  def killed(a: Term, b: Term) = Predicate("killed", List(a, b))
  def hates(a: Term, b: Term) = Predicate("hates", List(a, b))
  def richer(a: Term, b: Term) = Predicate("richer", List(a, b))
  def eq(a: Term, b: Term) = Predicate("=", List(a, b))

  val mansionMystery: Formula = And(
    List(
      Exists("x", And(List(lives(x), killed(x, a)))),
      And(
        List(
          lives(a),
          lives(b),
          lives(c),
          Forall("x", Implies(lives(x), Or(List(eq(x, a), eq(x, b), eq(x, c)))))
        )
      ),
      Forall(
        "x",
        Forall(
          "y",
          Implies(killed(x, y), And(List(hates(x, y), Neg(richer(x, y)))))
        )
      ),
      Forall("x", Implies(hates(a, x), Neg(hates(c, x)))),
      Forall("x", Implies(hates(a, x), Neg(eq(x, b)))),
      Forall("x", Implies(Neg(eq(x, b)), hates(a, x))),
      Forall("x", Implies(hates(b, x), Neg(richer(x, a)))),
      Forall("x", Implies(Neg(richer(x, a)), hates(b, x))),
      Forall("x", Implies(hates(a, x), hates(b, x))),
      Neg(Exists("x", Forall("y", hates(x, y)))),
      Neg(eq(a, b))
    )
  )

  /*
    To show that a formula phi is valid, we show that it's negation is unsatisfiable, i.e. !phi -> false.
    Hence if a Proof contains an empty clause, then the negation of the conjunction of all assumed clauses has to be valid
   */
  def extractTheorem(proof: ResolutionProof): Formula = {
    if (proof.exists(_._1.isEmpty))
      Neg(
        And(
          proof
            .filter(_._2 match {
              case Assumed                  => true
              case Deduced(premices, subst) => false
            })
            .map(_._1)
            .map(Or)
        )
      )
    else throw new Exception("The proof did not succeed")
  }

  def P(a: Term) = Predicate("P", List(a))
  def R(a: Term, b: Term) = Predicate("R", List(a, b))
  def f(a: Term, b: Term) = Function("f", List(a, b))
  def s1(a: Term) = Function("s1", List(a))
  val s2 = Function("s2", List())

  val exampleFromCourse: Formula = {
    val f1 = Forall("x", Exists("y", R(x, y)))
    val f2 =
      Forall("x", Forall("y", Implies(R(x, y), Forall("z", R(x, f(y, z))))))
    val f3 = Forall("x", Or(List(P(x), P(f(x, a)))))
    val f4 = Exists("x", Forall("y", And(List(R(x, y), P(y)))))
    Neg(Implies(And(List(f1, f2, f3)), f4))
  }

  val exampleFromCourseResult: List[Clause] = {
    val c1 = List(R(x, s1(x)))
    val c2 = List(Neg(R(x, y)), R(x, f(y, z)))
    val c3 = List(P(x), P(f(x, a)))
    val c4 = List(Neg(R(s2, y)), Neg(P(y)))
    List(c1, c2, c3, c4)
  }

}

object Runner extends App {
  import Lab04._

  val f = exampleFromCourse

  println("Unique names:")
  val r0 = makeVariableNamesUnique(f)
  printTree(r0)(1)
  println("NNF:")
  val r1 = negationNormalForm(f)
  // printTree(r1)(1)
  println("Skolem:")
  val r2 = skolemizationNegation(r1)
  printTree(r2)(1)

  println("PrenexSkolem:")
  val r3 = prenexSkolemizationNegation(r2)
  printTree(r3)(1)

  println("Clauses: ")
  val r4 = conjunctionPrenexSkolemizationNegation(r3)

  
  r4.foreach { printClause(_) }
  // // val f =
  // println("Hello")
}
