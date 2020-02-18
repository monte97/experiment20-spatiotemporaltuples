package it.unibo.casestudy

import alice.tuprolog._

object Scala2P {
  def createTheory(clauses: String*): Theory = new Theory(clauses mkString " ")
  def extractTerm(t: Term, i:Integer): Term = t.asInstanceOf[Struct].getArg(i).getTerm
  def solve(theory: Theory , goal:String): Stream[Term] = new Iterable[Term]{
    val engine = new Prolog
    engine.setTheory(theory)
    override def iterator: Iterator[Term] = new Iterator[Term]{
      var solution = engine.solve(goal);
      override def hasNext = solution.isSuccess || solution.hasOpenAlternatives
      override def next() = try solution.getSolution finally solution = engine.solveNext
      ();
    }
  }.toStream
}

object TupleSupport extends App {
  val engine = new Prolog()
  // val template = engine.toTerm("f(X).")
  val theory = new Theory("f(1).\nf(2).")
  println(Scala2P.solve(theory, "f(X).").toList)
}
