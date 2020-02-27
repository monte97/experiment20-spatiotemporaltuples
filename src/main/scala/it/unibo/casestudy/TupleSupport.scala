package it.unibo.casestudy

import alice.tuprolog._
import scala.collection.JavaConverters._
import scala.collection.mutable

object TupleSupport extends App with TupleSpace {
  addTuple("f(1)")
  addTuple("f(2)")
  println(solveFirst("f(X,Y)"))
  println(solve("f(X)"))
  println(exists("f(X)"))
  println(solveFirst("f(X)"))
  removeTuple("f(1)")
  println(exists("f(X)"))
  removeTuple("f(2)")
  println(exists("f(X)"))
}

trait TupleSpace {
  val tupleSpace = new Prolog("")
  val SOLUTION = "__solution__"

  def addTupleIfNotAlreadyThere(clause: String) = {
    if(!exists(clause)){
      addTuple(clause)
    }
  }

  def addTuple(clause: String) =
    tupleSpace.getTheoryManager.assertA(clause, true, null, false)

  def removeTuple(clause: String) =
    tupleSpace.getTheoryManager.retract(clause)

  def exists(goal: String) =
    tupleSpace.solve(goal).isSuccess

  def solveWithMatch(goal: String, variable: String): Option[String] = {
    solveFirst(goal).flatMap(_.bindings.get(variable))
  }

  def solveWithMatches(goal: String): Map[String,String] = {
    val solution = solveFirst(goal)
    solution.map(s => Map(SOLUTION->s.solution) ++ s.bindings).getOrElse(Map.empty)
  }

  def solveWithMatchesOpt(goal: String, vars: String*): Option[Seq[String]] = {
    val map = solveWithMatches(goal)
    if(map.isEmpty) None else Some(vars.map(v => map.get(v).get))
  }

  def solutionsWithMatches(goal: String): List[Map[String,String]] = {
    val solution = solve(goal)
    solution.map(s => Map(SOLUTION->s.solution) ++ s.bindings)
  }

  def solveFirst(goal: String): Option[TupleSolution] = {
    val solveInfo = tupleSpace.solve(goal)
    if(solveInfo.isSuccess){
      val vars = solveInfo.getBindingVars.asScala.map(_.getName)
      Some(TupleSolution(solveInfo.getSolution.toString, vars.map(varName => varName -> solveInfo.getVarValue(varName).toString).toMap))
    } else {
      None
    }
  }

  def solve(goal: String): List[TupleSolution] = {
    var solveInfo = tupleSpace.solve(goal)
    var result: List[TupleSolution] = List.empty
    while(solveInfo != null && solveInfo.isSuccess){
      val vars = solveInfo.getBindingVars.asScala.map(_.getName)
      result = TupleSolution(solveInfo.getSolution.toString, vars.map(varName => varName -> solveInfo.getVarValue(varName).toString).toMap) :: result
      if(solveInfo.hasOpenAlternatives) {
        solveInfo = tupleSpace.solveNext()
      } else {
        solveInfo = null
      }
    }
    result
  }
}

case class TupleSolution(solution: String, bindings: Map[String,String]) {
  def isEmpty = bindings.isEmpty
}