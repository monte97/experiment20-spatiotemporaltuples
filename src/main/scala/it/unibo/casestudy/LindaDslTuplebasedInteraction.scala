package it.unibo.casestudy

import alice.tuprolog.{Prolog, Term, Theory}
import it.unibo.alchemist.model.implementations.positions.Euclidean2DPosition
import it.unibo.alchemist.model.scafi.ScafiIncarnationForAlchemist._
import it.unibo.scafi.space.{Point2D, Point3D}

import scala.collection.JavaConverters._


object LindaDslTuplebasedInteractionTupleSupport {
  type Tuple = String
  type TupleTemplate = String

  case class SituatedTuple(tuple: Tuple, situation: SpatiotemporalSituation)
  case class SituatedTupleTemplate(tupleTemplate: TupleTemplate, situation: SpatiotemporalSituation)

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

  case class TupleOpId(uid: String)(val op: TupleOp) {
    override def toString: Tuple = uid
  }
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

class LindaDslTuplebasedInteraction extends AggregateProgram with TupleSpace with StandardSensors with ScafiAlchemistSupport with AlchemistLocationFix
  with Gradients with BlockG with FieldCalculusSyntax with FieldUtils with CustomSpawn with BlockS with BlockC {
  import LindaDslTuplebasedInteractionTupleSupport._

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
    val taskStealer = mid == 4 || mid == 13 || mid == 97
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
      when(doReadTask) { in("task(X)" @@@ AroundMe(50)) }.evolve((tuple: Tuple)  => {
        out(s"currentTask(${tuple})" @@ Me)
      }).evolve((tuple: Tuple) => {
        out(s"done(device(${mid}),${tuple})" @@ AroundMe(30))
      })
    }

    process(taskReader){
      when(doReadTask){ rd("task(X)" @@@ Everywhere) }.evolve((tuple: Tuple)  => {
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
      case SpatiotemporalSituation(AroundMe(ext),_) => OutMe(tuple.tuple, mid, ext)
      case SpatiotemporalSituation(region: Region,_) => OutInRegion(tuple.tuple, mid, region)
      case _ => ???
    })

    def rd(tupleTemplate: SituatedTupleTemplate): TupleOpId = TupleOpId(s"${mid}_rd_${tupleTemplate.hashCode()}")(tupleTemplate.situation match {
      case SpatiotemporalSituation(AroundMe(ext),_) => Read(tupleTemplate.tupleTemplate, mid, extension = ext)
      case SpatiotemporalSituation(region: Region,_) => Read(tupleTemplate.tupleTemplate, mid, extension = 20) // TODO
      case _ => ???
    })

    def in(tupleTemplate: SituatedTupleTemplate): TupleOpId = TupleOpId(s"${mid}_in_${tupleTemplate.hashCode()}")(tupleTemplate.situation match {
      case SpatiotemporalSituation(AroundMe(ext),_) => In(tupleTemplate.tupleTemplate, mid, extension = ext)
      case SpatiotemporalSituation(region: Region,_) => In(tupleTemplate.tupleTemplate, mid, extension = 20) // TODO
      case _ => ???
    })

    implicit class RichProcessOutput(pout: Map[TupleOpId,OperationResult]) {
      def continue(continuation: OperationResult => TupleOpId): Map[TupleOpId,OperationResult] = {
        sspawn(tupleOperation _, pout.map(v => continuation(v._2).prepend(v._1.uid)).toSet, ProcArg())
      }

      def andNext(continuation: Tuple => Unit): Unit = {
        pout.foreach(v => v._2.result.foreach(r => continuation(r)))
      }

      def evolve(continuation: Tuple => TupleOpId): Map[TupleOpId,OperationResult] = {
        sspawn(tupleOperation _, pout.flatMap(v => v._2.result.map(continuation(_).prepend(v._1.uid))).toSet, ProcArg())
      }
    }

    implicit class RichTupleOpId(toid: TupleOpId) {
      def prepend(s: String): TupleOpId = toid.copy(uid = s"${s}_${toid.uid}")(toid.op)
    }

    implicit class RichTuple(tuple: Tuple) {
      def @@(situation: SpatialSituation): SituatedTuple = SituatedTuple(tuple, situation)
    }

    implicit class RichTupleTemplate(template: TupleTemplate) {
      def @@@(situation: SpatialSituation): SituatedTupleTemplate = SituatedTupleTemplate(template, situation)
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
    val choice = rep[Option[T]](None){ v => v.filter(collect.contains(_)).orElse(collect.headOption) }
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

    val status = res._2
    node.put(toid.uid+"_op", toid.op + s"{$k}")
    node.put(toid.uid+"_status", (if(status==Output) 2 else if(status==Bubble) 1 else if(status==Terminated) 3 else 0)+s" {$k}")
    // println(s"[$mid] $toid -> $res")
    res
  }

  override def sspawn[A, B, C](process: A => B => (C, Status), params: Set[A], args: B): Map[A,C] = {
    spawn[A,B,Option[C]]((p: A) => (a: B) => {
      val (finished, result, status) = rep((false, none[C], false)) { case (finished, _, _) => {
        val (result, status) = process(p)(a)
        val newFinished = status == Terminated | includingSelf.anyHood(nbr{finished})
        val terminated = includingSelf.everyHood(nbr{newFinished})
        val (newResult, newStatus) = (result, status) match {
          case _ if terminated     => (None, false)
          case (_,     External)   => (None, false)
          case (_,     Terminated) => (None, true)
          case (value, Output)     => (Some(value), true)
          case (_,     Bubble)     => (None, true)
        }
        (newFinished, newResult, newStatus)
      } }
      val exitTuple = s"""exit("${p}")"""
      if(!status){ addTupleIfNotAlreadyThere(exitTuple) } else { removeTuple(exitTuple) }
      (result, status)
    }, params, args).collect { case (k, Some(p)) => k -> p }
  }


  def OutMeLogic(toid: TupleOpId, outOp: OutMe, arg: ProcArg): (OperationResult, Status) = {
    val OutMe(s, initiator, extension) = outOp
    val g = classicGradient(initiator==mid)
    val inRegion = g<=extension

    val terminate = branch(inRegion){ handleRemovalByIN(toid, initiator, s, g) }{ false }
    branch(inRegion){ once{ addTupleIfNotAlreadyThere(s) } }{ None }
    branch(terminate){ once {
      // println(s"${mid} > OUT > remove tuple $s");
      removeTuple(s)
    } }{ None }
    // if(terminate){ println(s"${toid.uid} > ${mid} > OUT $s > terminate [$toid] {$k}") }
    (OperationResult(OperationStatus.completed, Some(s)), if(terminate) Terminated else if(inRegion) Output else External)
  }

  def handleRemovalByIN(toid: TupleOpId, initiator: ID, s: Tuple, g: Double): Boolean = {
    object OutPhase extends Enumeration {
      type OutPhase = Value
      val NORMAL, SERVING, CLOSING = Value
    }
    import OutPhase._

    rep(NORMAL)(p => {
      var phase = p
      val leader = initiator==mid
      branch(phase!=CLOSING) {
        var processesWhoDidIN: List[Map[String, String]] = solutionsWithMatches(TupleRemovalRequested.matchTemplate).map(_.mapValues(_.stripQuotes))
        // println(s"${toid.uid} > ${mid} > OUT > $processesWhoDidIN asked for tuple $s")
        processesWhoDidIN = processesWhoDidIN.filter(retrieverMap => {
          val pid = retrieverMap(TupleRemovalRequested.By).stripQuotes
          val template = retrieverMap(TupleRemovalRequested.Template).stripQuotes
          val forThisTuple = new Prolog().`match`(Term.createTerm(s), Term.createTerm(template))
          val exited = exists(s"""exit(${pid.quoted})""")
          if (exited) removeTuple(TupleRemovalRequested.matchingTemplate(pid.quoted, template.quoted))
          !exited && forThisTuple
        })
        // println(s"${toid.uid} > ${mid} > OUT > choosing the first of filtered $processesWhoDidIN")
        val retrieverData: Option[Map[String, String]] =  processesWhoDidIN.headOption // keepUnless[Map[String, String]](processesWhoDidIN.headOption, r => !processesWhoDidIN.exists(_.get(TupleRemovalRequested.By) == r))
        val retriever = retrieverData.flatMap(_.get(TupleRemovalRequested.By))
        val template: Option[TupleTemplate] = retrieverData.flatMap(_.get(TupleRemovalRequested.Template))
        val chosenRetriever: Option[String] = consensus(data = retriever, leader = leader, potential = g)
        // chosenRetriever.foreach(r => println(s"${toid.uid} > $mid > OUT > $s > consensus on retriever: $r {$k}"))
        val supposedRetriever = chosenRetriever.getOrElse("").quoted
        if (leader) {
          val alreadyGivenTo: Option[String] = solveWithMatch(s"alreadyGiven(${toid.uid.quoted},By)", "By").map(_.stripQuotes)
          val exited = alreadyGivenTo.map(pid => exists(s"""exit(${pid.quoted})""")).getOrElse(false)
          if(exited){
            val markToRemove = s"alreadyGiven(${toid.uid.quoted},${alreadyGivenTo.get.quoted})"
            removeTuple(markToRemove)
            val eventToRemove = TupleRemovalOk(toid.uid, alreadyGivenTo.get, s)
            retractEvent(toid, eventToRemove)
            // println(s"${toid.uid} > $mid > OUT > however $alreadyGivenTo exited!!!! {$k}\nRemoving ${markToRemove} and event ${eventToRemove}")
          }
          val alreadyGiven = alreadyGivenTo.isDefined && !exited
          // if(alreadyGiven){ println(s"${toid.uid} > $mid > OUT > $s was already given to $alreadyGivenTo {$k}") }
          chosenRetriever.foreach(r => if (!alreadyGiven) {
            addTuple(s"alreadyGiven(${toid.uid.quoted},${supposedRetriever})")
            // println(s"${toid.uid} > $mid > OUT > $s > giving tuple $s to retriever $r {$k}")
            emitEvent(toid, TupleRemovalOk(toid.uid, r, s))
          })
        }
        val inProcessDone: Map[String, String] = solveWithMatches(TupleRemovalDone.matchingTemplate(TupleRemovalDone.By, toid.uid.quoted)).mapValues(_.stripQuotes)
        // val inProcessDoneBy = inProcessDone.get(TupleRemovalDone.By)
        if (!inProcessDone.isEmpty) {
          // println(s"${toid.uid} > $mid > OUT > $s > closing since got $inProcessDone {$k}")
          phase = CLOSING
        }
        phase
      }{ p }
    }) == CLOSING
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
    node.put(s"${toid.uid}_g", g)
    node.put(s"${toid.uid}_ext", extension)


    trait InPhase
    object InPhase {
      case object InPhaseStart extends InPhase
      val Start: InPhase = InPhaseStart
      case object InPhaseReading extends InPhase
      val Reading: InPhase = InPhaseReading
      case object InPhaseDone extends InPhase
      val Done: InPhase = InPhaseDone
    }
    import InPhase._

    val (phase,by,result) = rep[(InPhase,Option[String],Option[Tuple])]((Start,None,None)){ case (p,outProc,theTuple) => {
      var phase = p
      if (phase == Start) {
        emitEvent(toid, TupleRemovalRequested(toid.uid, ttemplate))
      } //else { retractEvent(inRequestToOut) }
      val tupleToRemove: Map[String, String] = solveWithMatches(TupleRemovalOk.matchingTemplate(TupleRemovalOk.By,toid.uid.quoted,TupleRemovalOk.Tuple)).mapValues(_.stripQuotes)
      val by = outProc.orElse(tupleToRemove.get(TupleRemovalOk.By))
      val tuple = theTuple.orElse(tupleToRemove.get(TupleRemovalOk.Tuple)) // get tuple only if this process is the one chosen by the OUT
      // tuple.foreach(tuple => println(s"${toid.uid} > ${mid} > IN > I can remove tuple $tuple from $by {$k}"))
      val result = consensus[(String,Tuple)]((by,tuple).insideOut, mid==initiator, g)
      // result.foreach { r => println(s"${toid.uid} > ${mid} > IN > consensus on removing tuple ${r._1} from ${r._2} {$k}") }
      if (result.isDefined) phase = Reading

      if (mid == initiator && result.isDefined) addTupleIfNotAlreadyThere(result.get._2)
      val didRead: Option[(String,Tuple)] = broadcastUnbounded(mid == initiator, result)
      val intermediaryGotAckFromReader = (for(intermediaryOutProc <- by; (chosenOutProc,_) <- didRead) yield intermediaryOutProc==chosenOutProc).getOrElse(false)
      if (intermediaryGotAckFromReader) {
        // println(s"${toid.uid} > $mid > IN > the initiator $initiator did read the tuple $tuple: emitting TupleRemovalDone {$k}");
        emitEvent(toid, TupleRemovalDone(toid.uid, didRead.get._1))
      }
      val ensureOutTermination = true // && localProcs.forall(lp => outProcess.map(_!=lp).getOrElse(true)))
      val done = broadcastUnbounded(intermediaryGotAckFromReader, intermediaryGotAckFromReader && ensureOutTermination)
      if (done) phase = Done
      (phase, by, result.map(_._2))
    }}
    node.put(s"${toid}_phase", phase + s" {$k}")
    node.put(s"${toid}_done", (phase==Done) + s" {$k}")

    (OperationResult(if(result.isDefined) OperationStatus.completed else OperationStatus.inProgress, result), if(mid==initiator){
      if(phase==Done) {
        clearEvents(toid)
        Terminated
      } else Output // if(mid==initiator) Output else Bubble
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
  def keep[T](expr: Option[T]): Option[T] = rep[Option[T]](None){ _.orElse(expr) }
  def keepUnless[T](expr: Option[T], reset: T=>Boolean): Option[T] = rep[Option[T]](None){ old => if(old.map(reset).getOrElse(false)) {
    print("#")
    None
  } else old.orElse(expr) }
  def keep(expr: Boolean): Boolean = rep(false)(b => if(b) b else expr)
  def unchanged[T](value: T): Boolean = rep(value,true)( v => (value,value==v._1))._2
  def delay[T](value: T, default: T): T = rep((default,default)){ case (old,_) => (value,old) }._2

  implicit class MyRichStr(s: String){
    def stripQuotes = s.stripPrefix("'").stripSuffix("'")
    def quoted = s"'$s'"
  }

  implicit class Tuple2Opt[A,B](t: (Option[A],Option[B])){
    def insideOut: Option[(A,B)] = for(a <- t._1; b <- t._2) yield (a,b)
  }
}


