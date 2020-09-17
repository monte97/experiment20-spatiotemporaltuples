package montelli

/*
 * Copyright (C) 2016-2019, Roberto Casadei, Mirko Viroli, and contributors.
 * See the LICENSE file distributed with this work for additional information regarding copyright ownership.
*/

package sims

import it.unibo.scafi.incarnations.BasicSimulationIncarnation.{AggregateProgram, BlockC, BlockG, Builtins, Gradients, FieldUtils}
import it.unibo.scafi.simulation.frontend.{Launcher, Settings}
import it.unibo.scafi.lib.StdLib_BlockG

object BasicDemo extends Launcher {
  // Configuring simulation
  Settings.Sim_ProgramClass = "sims.BasicProgram" // starting class, via Reflection
  Settings.ShowConfigPanel = false // show a configuration panel at startup
  Settings.Sim_NbrRadius = 0.15 // neighbourhood radius
  Settings.Sim_NumNodes = 10 // number of nodes
  launch()
}

class BasicProgram extends AggregateProgram with SensorDefinitions with BlockG with FieldUtils {
  //questo è il processo che gestisce le tuple
  override def main(): Any = {
    //ipotesi: ogni device ha una sola tupla
    var map: Map[Int, Int] = Map(mid -> mid * 2)

    branch(mid == 0) {
      map = map + (666 -> 999)
      map
    } {
      map
    }

    (mid,
      //condivido con i vicini tutte le informazioni che ho
      includingSelf.mergeHoodFirst(nbr(map))
    )

  }
}
