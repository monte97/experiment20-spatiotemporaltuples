package montelli


import it.unibo.casestudy.CorrectnessSupport.{In, OperationResult, OutInRegion, OutMe, ProcArg, Read, SituatedTuple, SituatedTupleTemplate, Tuple, TupleOpId, TupleTemplate}
import it.unibo.casestudy.{AroundMe, Region, SpatialSituation, TupleSpace}
import it.unibo.scafi.lib.StandardLibrary

trait Lib_LindaDSL {
  self: StandardLibrary.Subcomponent with Lib_ExecSupport =>
  trait LindaDSL {
    self: FieldCalculusSyntax with CustomSpawn with ExecSupport =>
    var enabled = false

    def process(condition: => Boolean)(expr: => Any): Any = {
      enabled = condition
      val res = expr
      enabled = false
      res
    }


    def when(condition: => Boolean)(expr: => TupleOpId): Map[TupleOpId,OperationResult] = {
      val c = enabled && condition
      val toid: Set[TupleOpId] = if(goesUp(c)) Set(expr) else Set.empty
      sspawn(tupleOperation _, toid, ProcArg())
    }

    def when[T](gen: => Option[T])(expr: T => TupleOpId): Map[TupleOpId,OperationResult] = {
      val toid: Option[TupleOpId] = gen.filter(_ => enabled).map(expr)
      sspawn(tupleOperation _, toid.toSet, ProcArg())
    }

    def out(tuple: SituatedTuple): TupleOpId = TupleOpId(s"${mid}_out_${tuple.hashCode()}")(tuple.situation match {
      case AroundMe(ext) => OutMe(tuple.tuple, mid, ext)
      case region: Region => OutInRegion(tuple.tuple, mid, region)
    })

    def rd(tupleTemplate: SituatedTupleTemplate): TupleOpId = TupleOpId(s"${mid}_rd_$k")(tupleTemplate.situation match {
      case AroundMe(ext) => Read(tupleTemplate.tupleTemplate, mid, extension = ext)
      case region: Region => Read(tupleTemplate.tupleTemplate, mid, extension = 20) // TODO
    })

    def in(tupleTemplate: SituatedTupleTemplate): TupleOpId = TupleOpId(s"${mid}_in_$k")(tupleTemplate.situation match {
      case AroundMe(ext) => In(tupleTemplate.tupleTemplate, mid, extension = ext)
      case region: Region => In(tupleTemplate.tupleTemplate, mid, extension = 20) // TODO
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

}