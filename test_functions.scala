object Test{
  val a = 2
  val b = 3

  def testfun(a1: Int, arg: Int = 0): Int = 42

  /*def funct1(arg1: Int, arg2: Int): String = {
    val f11: String = "smaller"
    val f12: String = "greater"

    if(arg1 + arg2 > 0) f12 else f11
  }

  def funct2(arg1: Int, arg2: Int): String = {
    val f11: String = "smaller"
    val f12: String = "greater"

    if(arg1 + arg2 > 0) f12 else f11
  }*/

  /*def from(): Int =  {
    def in(a: Int, b: Int): Int = a
    in(2, 3)
  }
  def to(): Int = {
    def in(a: Int): Int = a
    in(5)
  }*/

  /*def from(): Int =  {
    def in(a: Int, b: Int): Int = a
    in(2, 3)
  }
  def to(): Int = {
    def ins(a: Int): Int = a
    ins(3)
  }*/

  /*def from(): Int =  {
    def in(a: Int, b: Int): Int = a
    in(2, 3)
  }
  def to(): Int = {
    def in(a: Int): Int = a
    in(2)
  }*/

  def to(): Int =  {
    def in(a: Int, b: Int): Int = a
    in(2, 3)
  }
  def from(): Int = {
    def in(a: Int): Int = a
    in(2)
  }

  //def sub(): Int = 5 * 8
}
