package it.unibo.casestudy

import it.unibo.alchemist.model.implementations.positions.Euclidean2DPosition
import it.unibo.alchemist.model.scafi.ScafiIncarnationForAlchemist._
import it.unibo.scafi.space.{Point2D, Point3D}
import scala.collection.JavaConverters._


class Workflow extends AggregateProgram with StandardSensors with Gradients with BlockG with ScafiAlchemistSupport
  with FieldCalculusSyntax with FieldUtils with CustomSpawn with BlockS with BlockC {

  override def main(): Any = {
    spawn[Int,Int,Int](k => a => (k,true), Set(mid), 0)
      .continueWith[Int,Int,Double](k => a => (k+1.0, true), x => if(x==5) Some(x * 1000) else None, m => 0)
  }

  type Process[K,A,R] = K => A => (R, Boolean)

  implicit class RichProcessOutput[K,V](pout: Map[K,V]) {
    def continueWith[K2,A2,R2](process: Process[K2,A2,R2], keyGen: K=>Option[K2], argGen: Map[K,V]=>A2): Map[K2,R2] = {
      spawn[K2,A2,R2](process, pout.keySet.flatMap(keyGen(_)), argGen(pout))
    }
  }

}