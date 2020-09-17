package montelli

import it.unibo.scafi.lib.StandardLibrary

trait Lib_ExecSupport {
  self: StandardLibrary.Subcomponent =>

  trait ExecSupport {
    self: AggregateProgram => {
      def once[T](expr: => T): Option[T] = rep((true,none[T])){ case (first,value) => (false, if(first) Some(expr)  else None) }._2
      def none[T]: Option[T] = None
      def keepOpt[T](expr: Option[T]): Option[T] = rep[Option[T]](None){ _.orElse(expr) }
      def keepUnless[T](expr: Option[T], reset: T=>Boolean): Option[T] = rep[Option[T]](None){ old => if(old.exists(reset)) {
        // print("#")
        None
      } else old.orElse(expr) }
      def keepBool(expr: Boolean): Boolean = rep(false)(b => if(b) b else expr)
      def unchanged[T](value: T): Boolean = rep(value,true)( v => (value,value==v._1))._2
      def delay[T](value: T, default: T, nrounds: Int = 1): T = rep((default,default,0)){
        case (old,_,k) => (if(k<nrounds) old else value, old, k+1)
      }._2
      def goesUp(c: Boolean): Boolean = rep((false,false)){ case (oldRes,oldC) => (!oldC && c, c) }._1
      def stableFor[T](value: T): Int = rep((value,0)){ case (old,k) => (value, if(old==value) k+1 else 0) }._2
    }
  }
}
