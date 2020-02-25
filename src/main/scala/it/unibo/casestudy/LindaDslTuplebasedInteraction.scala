package it.unibo.casestudy

import alice.tuprolog.{Prolog, Term, Theory}
import it.unibo.alchemist.model.implementations.positions.Euclidean2DPosition
import it.unibo.alchemist.model.scafi.ScafiIncarnationForAlchemist._
import it.unibo.scafi.space.{Point2D, Point3D}

import scala.collection.JavaConverters._


object LindaTupleSupport {
  type Tuple = String
  type TupleTemplate = String

  case class SituatedTuple(tuple: Tuple, situation: Situation)
  case class SituatedTupleTemplate(tupleTemplate: TupleTemplate, situation: Situation)

  implicit def situateTuple(tuple: Tuple) = SituatedTuple(tuple, Me)
  implicit def situateTupleTemplate(tupleTemplate: TupleTemplate) = SituatedTupleTemplate(tupleTemplate, Me)

  trait Op
  object Op {
    val out: Op = new Op { override def toString: String = "out" }
    val rd: Op = new Op { override def toString: String = "rd" }
    val in: Op = new Op { override def toString: String = "in" }
  }

  trait TupleOp { val initiator: ID }
  case class OutMe(datum: Tuple, val initiator: ID, val extension: Double = 0) extends TupleOp
  case class OutHere(datum: Tuple, val initiator: ID, val position: Point2D, val extension: Double = 0) extends TupleOp
  case class OutInRegion(datum: Tuple, val initiator: ID, val region: Region) extends TupleOp
  case class Read(template: TupleTemplate, val initiator: ID, val extension: Double = Double.PositiveInfinity) extends TupleOp
  case class In(template: TupleTemplate, val initiator: ID, val extension: Double = Double.PositiveInfinity) extends TupleOp

  case class TupleOpId(uid: String)(val op: TupleOp)
  trait OperationStatus
  object OperationStatus {
    val inProgress: OperationStatus = new OperationStatus { }
    val completed: OperationStatus = new OperationStatus { }
  }
  case class OperationResult(operationStatus: OperationStatus, result: Option[Tuple])

  case class ProcArg(localTuples: Set[Tuple] = Set.empty, procs: Set[TupleOpId] = Set.empty)

  trait ProcessEvent

  case class TupleRemovalRequested(by: String, tuple: TupleTemplate) extends ProcessEvent {
    override val toString: TupleTemplate = s"""inRequested(by("${by}"),template("$tuple"))"""
  }
  object TupleRemovalRequested {
    val By = "Uid"
    val Template = "Template"
    val variables: List[String] = List(By,Template)
    def matchingTemplate(by: String, template: String): TupleTemplate = s"inRequested(by($by),template($template))"
    val matchTemplate = matchingTemplate(By,Template)
  }

  case class TupleRemovalOk(by: String, to: String, tuple: Tuple) extends ProcessEvent{
    override val toString: TupleTemplate = s"""inOk(by("${by}"),to("$to"),tuple("$tuple"))"""
  }
  object TupleRemovalOk {
    val By = "Uid"
    val To = "Template"
    val Tuple = "Tuple"
    val variables: List[String] = List(By,To,Tuple)
    def matchingTemplate(by: String, to: String, tuple: Tuple): TupleTemplate = s"inOk(by($by),to($to),tuple($tuple))"
    val matchTemplate = matchingTemplate(By,To,Tuple)
  }

  case class TupleRemovalDone(by: String, to: String) extends ProcessEvent {
    override val toString: TupleTemplate = s"""inDone(by("${by}"),to("$to"))"""
  }
  object TupleRemovalDone {
    val By = "Uid"
    val To = "Template"
    val variables: List[String] = List(By,To)
    def matchingTemplate(by: String, to: String): TupleTemplate = s"inDone(by($by),to($to))"
    val matchTemplate = matchingTemplate(By,To)
  }
}

class LindaDSL extends AggregateProgram with TupleSpace with StandardSensors with ScafiAlchemistSupport with AlchemistLocationFix
  with Gradients with BlockG with FieldCalculusSyntax with FieldUtils with CustomSpawn with BlockS with BlockC {
  import LindaTupleSupport._

  var k = 0

  val linda = new LindaDSL

  lazy val initialiseTasks = if(mid == 8 || mid == 117){
    addTuple(s"taskToGenerate(task(x$mid))")
    addTuple(s"taskToGenerate(task(y$mid))")
    addTuple(s"taskToGenerate(task(z$mid))")
  }

  override def main(): Any = {
    k = rep(0)(_+1)
    initialiseTasks
    val taskProposal: Option[String] = solveWithMatch("taskToGenerate(task(X))", "X")
    val task: Option[String] = solveWithMatch("currentTask(T)", "T")
    node.put("task", task)
    val taskGenerator = mid == 8 || mid == 117
    val taskStealer = mid == 7 || mid == 9 || mid == 97
    val taskReader = false // mid % 5 == 0
    // val doGenerateTask = taskGenerator && !taskProposal.isEmpty
    node.put("doGenerateTask", taskProposal.isDefined /* doGenerateTask */)
    val doReadTask = (taskStealer || taskReader) && task.isEmpty
    node.put("doReadTask", taskReader && doReadTask)
    node.put("doStealTask", taskStealer && doReadTask)

    import linda._

    process(taskGenerator){
      when(taskProposal){ t => out(s"task($t)") }.andNext((tuple: Tuple) => {
        removeTuple(s"taskToGenerate($tuple)")
      })
    }

    process(taskStealer){
      when(doReadTask) { in("task(X)") }.evolve((tuple: Tuple)  => {
        out(s"currentTask(${tuple})" @@ Me)
      }).evolve((tuple: Tuple) => {
        out(s"done(device(${mid}),${tuple})" @@ AroundMe(30))
      })
    }

    process(taskReader){
      when(doReadTask){ rd("task(X)") }.evolve((tuple: Tuple)  => {
        out(s"currentTask(${tuple})" @@ Me)
      }).evolve((tuple: Tuple) => {
        out(s"done(device(${mid}),${tuple})" @@ AroundMe(30))
      })
    }

    node.put("theory", tupleSpace.getTheory.toString)
  }

  class LindaDSL {
    var enabled = false
    def process(condition: => Boolean)(expr: => Any) = {
      enabled = condition
      val res = expr
      enabled = false
      res
    }

    def when(condition: => Boolean)(expr: => TupleOpId): Map[TupleOpId,OperationResult] = {
      val c = enabled && condition
      val toid = expr
      sspawn(tupleOperation _, if(c) Set(toid) else Set.empty, ProcArg())
    }

    def when[T](gen: => Option[T])(expr: T => TupleOpId): Map[TupleOpId,OperationResult] = {
      val toid: Option[TupleOpId] = gen.map(expr)
      sspawn(tupleOperation _, toid.toSet, ProcArg())
    }

    def out(tuple: SituatedTuple): TupleOpId = TupleOpId(s"${mid}_out_${tuple.hashCode()}")(tuple.situation match {
      case AroundMe(ext) => OutMe(tuple.tuple, mid, ext)
      case region: Region => OutInRegion(tuple.tuple, mid, region)
    })

    def rd(tupleTemplate: SituatedTupleTemplate): TupleOpId = TupleOpId(s"${mid}_rd_${tupleTemplate.hashCode()}")(tupleTemplate.situation match {
      case Me => Read(tupleTemplate.tupleTemplate, mid, extension = 20) // TODO
      case region: Region => Read(tupleTemplate.tupleTemplate, mid, extension = 20) // TODO
    })

    def in(tupleTemplate: SituatedTupleTemplate): TupleOpId = TupleOpId(s"${mid}_in_${tupleTemplate.hashCode()}")(tupleTemplate.situation match {
      case Me => In(tupleTemplate.tupleTemplate, mid, extension = 20) // TODO
      case region: Region => In(tupleTemplate.tupleTemplate, mid, extension = 20) // TODO
    })

    implicit class RichProcessOutput(pout: Map[TupleOpId,OperationResult]) {
      def continue(continuation: OperationResult => TupleOpId): Map[TupleOpId,OperationResult] = {
        val toid = continuation
        sspawn(tupleOperation _, pout.map(v => continuation(v._2).prepend(v._1.uid)).toSet, ProcArg())
      }

      def andNext(continuation: Tuple => Unit): Unit = {
        pout.foreach(v => v._2.result.foreach(r => continuation(r)))
      }

      def evolve(continuation: Tuple => TupleOpId): Map[TupleOpId,OperationResult] = {
        val toid = continuation
        sspawn(tupleOperation _, pout.flatMap(v => v._2.result.map(continuation(_).prepend(v._1.uid))).toSet, ProcArg())
      }
    }

    implicit class RichTupleOpId(toid: TupleOpId) {
      def prepend(s: String): TupleOpId = toid.copy(uid = s"${s}_${toid.uid}")(toid.op)
    }

    implicit class RichTuple(tuple: Tuple) {
      def @@(situation: Situation): SituatedTuple = SituatedTuple(tuple, situation)
    }
  }

  import Spawn._

  def consensusOn[T](data: Option[T], leader: Boolean, potential: Double): Boolean = {
    val collect = C[Double,Set[T]](potential, _++_, data.toSet, Set.empty)
    val choice = rep[Option[T]](None){ v => v.orElse(collect.headOption) }
    broadcastUnbounded(leader && !choice.isEmpty, choice) == data && !data.isEmpty
  }

  def consensus[T](data: Option[T], leader: Boolean, potential: Double): Option[T] = {
    val collect = C[Double,Set[T]](potential, _++_, data.toSet, Set.empty)
    val choice = rep[Option[T]](None){ v => v.orElse(collect.headOption) }
    broadcastUnbounded(leader && !choice.isEmpty, choice)
  }

  def tupleOperation(toid: TupleOpId)(arg: ProcArg): (OperationResult, Status) = {
    node.put(toid.uid, 1) // marker that a process instance has been executed

    val res = toid.op match {
      case outop@OutMe(s, initiator, extension) => OutMeLogic(toid, outop, arg)
      case outop@OutInRegion(s, initiator, region) => OutInRegionLogic(toid, outop, arg)
      case outop@OutHere(s, initiator, position, extension) => OutInRegionLogic(toid, OutInRegion(s, initiator, CircularRegion(position, extension)), arg)
      case readop@Read(ttemplate, initiator, extension) => ReadLogic(toid, readop, arg)
      case inop@In(ttemplate, initiator, extension) => InLogic(toid, inop, arg)
      case _ => ??? // (OperationResult("invalid"), Terminated)
    }

    node.put(toid.uid+"_op", toid.op)
    node.put(toid.uid+"_status", if(res._2==Output) 2 else if(res._2==Bubble) 1 else if(res._2==Terminated) 3 else 0)
    // println(s"[$mid] $toid -> $res")
    res
  }

  def OutMeLogic(toid: TupleOpId, outOp: OutMe, arg: ProcArg): (OperationResult, Status) = {
    val OutMe(s, initiator, extension) = outOp
    val g = classicGradient(initiator==mid)
    val terminate = handleRemovalByIN(toid, initiator, s, g)
    val inRegion = g<=extension
    branch(inRegion){ once{ addTupleIfNotAlreadyThere(s) } }{ None }
    branch(terminate){ once {
      // println(s"${mid} > OUT > remove tuple $s");
      removeTuple(s)
    } }{ None }
    if(terminate){ println(s"${mid} > OUT $s > terminate [$toid]") }
    (OperationResult(OperationStatus.completed, Some(s)), if(terminate) Terminated else if(inRegion) Output else External)
  }

  def handleRemovalByIN(toid: TupleOpId, initiator: ID, s: Tuple, g: Double): Boolean = {
    val leader = initiator==mid
    val processWhoDidIN: Map[String,String] = solveWithMatches(TupleRemovalRequested.matchTemplate).mapValues(_.stripQuotes) //keep { events.collectFirst { case ev@TupleRemovalRequested(tid, `s`) => ev }.map(_.by) }
    val retriever: Option[String] = processWhoDidIN.get(TupleRemovalRequested.By)
    val chosenRetriever: Option[String] = consensus(data = retriever, leader = leader, potential = g)
    chosenRetriever.foreach(r => println(s"$mid > OUT > $s > consensus on retriever: $r"))
    val template: Option[TupleTemplate] = branch(leader){ processWhoDidIN.get(TupleRemovalRequested.Template) }{ None }
    val chosenTuple: Option[Tuple] = template.flatMap(tt => if(new Prolog().`match`(Term.createTerm(s), Term.createTerm(tt))) Some(s) else None)
    chosenRetriever.foreach(r => if(chosenTuple.isDefined){
      println(s"$mid > OUT > $s > chosen tuple $chosenTuple for retriever $r")
      emitEvent(toid, TupleRemovalOk(toid.uid, r, chosenTuple.get))
    })
    val inProcessDone: Map[String,String] = solveWithMatches(TupleRemovalDone.matchingTemplate(TupleRemovalDone.By,toid.uid.quoted)).mapValues(_.stripQuotes)
    val inProcessDoneBy = inProcessDone.get(TupleRemovalDone.By)
    !inProcessDone.isEmpty
  }

  def OutInRegionLogic(toid: TupleOpId, outOp: OutInRegion, arg: ProcArg): (OperationResult, Status) = {
    val OutInRegion(s, initiator, region) = outOp
    val pos = currentPosition()
    val inRegion = region.withinRegion(Point2D(pos.x, pos.y))
    branch(inRegion){ once{ addTupleIfNotAlreadyThere(s) } }{ None }
    /* branch(terminate){ once { removeTuple(s) } }{ None } */
    (OperationResult(OperationStatus.completed, Some(s)), if(inRegion) Output else External)
  }

  def ReadLogic(toid: TupleOpId, readOp: Read, arg: ProcArg): (OperationResult, Status) = {
    val ProcArg(localTuples, localProcs) = arg
    val Read(ttemplate, initiator, extension) = readOp

    val g = classicGradient(initiator==mid)
    // node.put(s"${toid.uid}_g", g)
    val tupleFound = solveFirst(ttemplate) // localTupleMatching(localTuples, ttemplate)
    val result  = broadcastUnbounded[Option[TupleSolution]](!tupleFound.isEmpty, tupleFound)
    val (gotIt,canClose) = rep((false,false))(f => {
      val shouldBeDone = mid==initiator && !result.isEmpty
      (shouldBeDone, f._2 || (shouldBeDone && f._1))
    })
    result.foreach(sol => addTupleIfNotAlreadyThere(sol.solution))
    (OperationResult(if(result.isDefined) OperationStatus.completed else OperationStatus.inProgress, result.map(_.solution)), if(mid==initiator){
      if(canClose){ Terminated } else if(gotIt) { Output } else { Bubble }
    } else if(g<extension) { Bubble } else { External })
  }

  def InLogic(toid: TupleOpId, inOp: In, arg: ProcArg): (OperationResult, Status) = {
    val ProcArg(localTuples, localProcs) = arg
    val In(ttemplate, initiator, extension) = inOp
    // Note: IN is not trivial: Need consensus on the tuple to remove; As there might be multiple concurrent INs, these must be discriminated by a tuple's owner
    // So, it needs 2 feedback loops for 4 flows of events: 1) TupleRemovalRequested(by,tuple) -- 2) TupleRemovalOk(by) -- 3) TupleRemovalDone -- 4) TupleRemovalEnd
    val g = classicGradient(initiator==mid)

    trait InPhase
    object InPhase {
      case object InPhaseStart extends InPhase
      val Start: InPhase = InPhaseStart
    }
    import InPhase._

    rep(Start)(phase => {
      val inRequestToOut = TupleRemovalRequested(toid.uid, ttemplate)
      if(phase == Start){ emitEvent(toid, inRequestToOut) } //else { retractEvent(inRequestToOut) }
      phase
    })

    val tupleToRemove: Map[String,String] =  solveWithMatches(TupleRemovalOk.matchingTemplate(TupleRemovalOk.By,toid.uid.quoted,TupleRemovalOk.Tuple)).mapValues(_.stripQuotes)
    val by = tupleToRemove.get(TupleRemovalOk.By)
    val tuple = tupleToRemove.get(TupleRemovalOk.Tuple)
    if(!tupleToRemove.isEmpty){
      println(s"${mid} > IN > as ${toid.uid}, I can remove tuple $tuple from $by ")
    }

    // val canRetrieveTheTuple = broadcastUnbounded(intermediaryGotAckFromOut, intermediaryGotAckFromOut)
    val result  = broadcastUnbounded[Option[String]](tuple.isDefined, tuple)
    if(mid==initiator && result.isDefined) addTupleIfNotAlreadyThere(result.get)
    val didRead = broadcastUnbounded(mid==initiator, mid==initiator && !result.isEmpty)
    val intermediaryGotAckFromReader = keep { tuple.isDefined && didRead && by.isDefined  }
    if(intermediaryGotAckFromReader){
      println(s"$mid > IN > the initiator $initiator did read the tuple $tuple: emitting TupleRemovalDone [$toid]");
      emitEvent(toid, TupleRemovalDone(toid.uid, by.get))
    }
    val ensureOutTermination = true // && localProcs.forall(lp => outProcess.map(_!=lp).getOrElse(true)))
    val done = broadcastUnbounded(intermediaryGotAckFromReader, intermediaryGotAckFromReader && ensureOutTermination)
    node.put(s"${toid}_done", done)
    // IN bubble closing similar to read
    val (gotIt,canClose) = rep((false,false))(f => {
      val shouldBeDone = mid==initiator && !result.isEmpty && done
      (shouldBeDone, f._2 || (shouldBeDone && f._1))
    })
    /*
    if(canClose){
      println(s"$mid > IN > $result -- can close!!!!  [$toid]")
      addTupleIfNotAlreadyThere(result.get)
    }
     */
    (OperationResult(if(result.isDefined) OperationStatus.completed else OperationStatus.inProgress, result), if(mid==initiator){
      if(canClose) {
        clearEvents(toid)
        Terminated
      } else if(gotIt) Output else Bubble
    } else if(g<extension) Bubble else External)
  }

  var eventMaps: Map[TupleOpId,Set[String]] = Map.empty
  def emitEvent(toid: TupleOpId, event: ProcessEvent): Unit = {
    eventMaps += toid -> (eventMaps.getOrElse(toid,Set.empty) + event.toString)
    addTupleIfNotAlreadyThere(event.toString)
  }
  def clearEvents(toid: TupleOpId): Unit = {
    eventMaps.get(toid).foreach(t => t.foreach(removeTuple(_)))
    eventMaps += toid -> Set.empty
  }
  def retractEvent(toid: TupleOpId, event: ProcessEvent): Unit = removeTuple(event.toString)

  def broadcastUnbounded[V](source: Boolean, field: V): V =
    G[V](source, field, v => v, nbrRange _)

  // TODO: add to stdlib
  def once[T](expr: => T): Option[T] = rep((true,none[T])){ case (first,value) => (false, if(first) Some(expr)  else None) }._2
  def none[T]: Option[T] = None
  def keep[T](expr: => Option[T]): Option[T] = rep[Option[T]](None){ _.orElse(expr) }
  def keep(expr: => Boolean): Boolean = rep(false)(b => if(b) b else expr)
  def unchanged[T](value: T): Boolean = rep(value,true)( v => (value,value==v._1))._2

  implicit class MyRichStr(s: String){
    def stripQuotes = s.stripPrefix("'").stripSuffix("'")
    def quoted = s"'$s'"
  }
}


