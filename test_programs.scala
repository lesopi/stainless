//package stainless.collection

/*import stainless._
import stainless.lang._
import stainless.annotation._
import stainless.math._
import stainless.proof._*/

object prog1 {
  class Fact {
    def computeFactorial(num : Int) : Int = {
        if (num < 1)
           1
        else
           num * (this.computeFactorial(num - 1));
    }
  }

  class Test {
    def t(): Int = new Fact().computeFactorial(3)

    def u(): Int = 42
  }

  def a1[A](a0: A, arg: Int = 0): Int = {
    new Fact().computeFactorial(3)
  }
  def a2[A](a0: Int, a1: A, arg: Int = 0): Int = 5 + 42

  def a3(sm: Int, lg: Int): Int = {
    if(sm < 0) 42 else 89
  }
}

object prog2 {
  class Factorial {
    def computeFactorial(num : Int) : Int = {
        if (num < 1)
           1
        else
           num * (this.computeFactorial(num - 1));
    }
  }

  class Test {
    def t(): Int = new Factorial().computeFactorial(3)
  }
  def a1[A](a0: Int, arg: Int = 0): Int = {
    6
  }
  def b2[B](a0: Int): Int = 5 + 42

  def a3(sm: Int, lg: Int): Int = {
    if(sm > 0) 799 else -32
  }

  def jo(o: Option[Int]): Int = o match{
    case None => 0
    case Some(i) => i
  }

}
