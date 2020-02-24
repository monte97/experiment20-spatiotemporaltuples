package it.unibo.casestudy

import alice.tuprolog.{Prolog, Theory}
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
  case class TupleRemovalRequested(by: TupleOpId, tuple: Tuple) extends ProcessEvent
  case class TupleRemovalOk(by: TupleOpId) extends ProcessEvent
  case object TupleRemovalDone extends ProcessEvent
}

class LindaDSL extends AggregateProgram with TupleSpace with StandardSensors with ScafiAlchemistSupport with AlchemistLocationFix
  with Gradients with BlockG with FieldCalculusSyntax with FieldUtils with CustomSpawn with BlockS with BlockC {
  import LindaTupleSupport._

  var events: Set[ProcessEvent] = Set()
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
      when(taskProposal){ t => out(s"task($t)") }
    }

    process(taskStealer){
      when(doReadTask) { in("task(X)") }.evolve((tuple: Tuple)  => {
        out(s"currentTaskIn(${tuple})" @@ Me)
      }).evolve((tuple: Tuple) => {
        out(s"doneIn(device(${mid}),${tuple})" @@ AroundMe(30))
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
    node.put("events", events)
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

    def out(tuple: SituatedTuple): TupleOpId = TupleOpId(s"${mid}_out")(tuple.situation match {
      case AroundMe(ext) => OutMe(tuple.tuple, mid, ext)
      case region: Region => OutInRegion(tuple.tuple, mid, region)
    })

    def rd(tupleTemplate: SituatedTupleTemplate): TupleOpId = TupleOpId(s"${mid}_rd")(tupleTemplate.situation match {
      case Me => Read(tupleTemplate.tupleTemplate, mid, extension = 20) // TODO
      case region: Region => Read(tupleTemplate.tupleTemplate, mid, extension = 20) // TODO
    })

    def in(tupleTemplate: SituatedTupleTemplate): TupleOpId = TupleOpId(s"${mid}_in")(tupleTemplate.situation match {
      case Me => In(tupleTemplate.tupleTemplate, mid, extension = 20) // TODO
      case region: Region => In(tupleTemplate.tupleTemplate, mid, extension = 20) // TODO
    })

    implicit class RichProcessOutput(pout: Map[TupleOpId,OperationResult]) {
      def continue(continuation: OperationResult => TupleOpId): Map[TupleOpId,OperationResult] = {
        val toid = continuation
        sspawn(tupleOperation _, pout.map(v => continuation(v._2).prepend(v._1.uid)).toSet, ProcArg())
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

    node.put(toid.uid+"_status", if(res._2==Output) 2 else if(res._2==Bubble) 1 else 0)
    // println(s"[$mid] $toid -> $res")
    res
  }

  def OutMeLogic(toid: TupleOpId, outOp: OutMe, arg: ProcArg): (OperationResult, Status) = {
    val OutMe(s, initiator, extension) = outOp
    val g = classicGradient(initiator==mid)
    val (inRequestor, terminate) = handleRemovalByIN(toid, initiator, s, g)
    val inRegion = g<=extension
    branch(inRegion){ once{ addTupleIfNotAlreadyThere(s) } }{ None }
    branch(terminate){ once {
      // println(s"${mid} > OUT > remove tuple $s");
      removeTuple(s)
    } }{ None }
    // if(terminate){ println(s"${mid} > OUT > terminate [$toid]") }
    (OperationResult(OperationStatus.completed, Some(s)), if(terminate) Terminated else if(inRegion) Output else External)
  }

  def handleRemovalByIN(toid: TupleOpId, initiator: ID, s: Tuple, g: Double): (Option[ID], Boolean) = {
    val processWhoDidIN = keep { events.collectFirst { case ev@TupleRemovalRequested(tid, `s`) => ev }.map(_.by) }
    // processWhoDidIN.foreach { pin => println(s"$mid > OUT > got process $pin who did IN") }
    val gotConfirmation = consensusOn(data = processWhoDidIN, leader = initiator==mid, potential = g)
    processWhoDidIN.foreach(p => if(gotConfirmation) {
      // println(s"$mid > OUT > got consensus on process who did IN and emitted event TupleRemovalOk")
      emitEvent(TupleRemovalOk(toid))
    })
    // Return whether the OUT process must terminate (i.e., we are done) or not
    val gotAck = events.collectFirst { case TupleRemovalDone => true }.getOrElse(false)
    // if(gotAck){ println(s"$mid > OUT > got ACK from process who did IN") }
    (processWhoDidIN.map(_.op.initiator), gotAck)
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
    // So, it needs 2 feedback loops for 4 flows of events:
    // 1) TupleRemovalRequested(by,tuple) -- 2) TupleRemovalOk(by) -- 3) TupleRemovalDone -- 4) TupleRemovalEnd
    val g = classicGradient(initiator==mid)
    val tupleFound = solveFirst(ttemplate)
    val myTupleChosen = consensusOn(tupleFound, initiator==mid, g)
    if(myTupleChosen){
      // Once the device who found the tuple sees that its tuple is the chosen one, it must get confirmation by tuple's owner
      // Tuple removal must affect Out processes
      // println(s"$mid > IN > my tuple was chosen: emitting event TupleRemovalRequested")
      emitEvent(TupleRemovalRequested(toid, tupleFound.get.solution))
    }
    val outProcess = events.collectFirst[TupleOpId]{ case TupleRemovalOk(by) => by }
    val gotAck = !outProcess.isEmpty
    // if(gotAck){ println(s"$mid > IN > got ack for retrieval: TupleRemovalOk(by ${outProcess.get})") }
    val canRetrieveTheTuple = broadcastUnbounded(gotAck, gotAck)
    val result  = broadcastUnbounded[Option[String]](myTupleChosen && canRetrieveTheTuple, tupleFound.map(_.solution))
    val didRead = broadcastUnbounded(mid==initiator, mid==initiator && !result.isEmpty)
    if(myTupleChosen && didRead){
      // println(s"$mid > IN > the initiator did read the tuple: emitting TupleRemovalDone");
      emitEvent(TupleRemovalDone)
    }
    val done = broadcastUnbounded(myTupleChosen && didRead, (myTupleChosen && didRead) && localProcs.forall(lp => outProcess.map(_!=lp).getOrElse(true)))
    // IN bubble closing similar to read
    val (gotIt,canClose) = rep((false,false))(f => {
      val shouldBeDone = mid==initiator && !result.isEmpty && done
      (shouldBeDone, f._2 || (shouldBeDone && f._1))
    })
    (OperationResult(if(result.isDefined) OperationStatus.completed else OperationStatus.inProgress, result), if(mid==initiator){
      if(canClose) Terminated else if(gotIt) Output else Bubble
    } else if(g<extension) Bubble else External)
  }

  def emitEvent(event: ProcessEvent): Unit = {
    events += event
  }

  def broadcastUnbounded[V](source: Boolean, field: V): V =
    G[V](source, field, v => v, nbrRange _)

  // TODO: add to stdlib
  def once[T](expr: => T): Option[T] = rep((true,none[T])){ case (first,value) => (false, if(first) Some(expr)  else None) }._2
  def none[T]: Option[T] = None
  def keep[T](expr: => Option[T]): Option[T] = rep[Option[T]](None){ _.orElse(expr) }
}


