/* Copyright 2009-2016 EPFL, Lausanne */

package stainless
package BAProject


/* This algorithm computes the solution to the General Assignment Problem with
 * the Hungarian method. This method solves the balanced assignment problem,
 * i.e the problem where there is the same number of assignees and jobs.
 * If the problem is not balanced it has to be transformed into a balances one
 * by adding dummy rows or columns to the cost matrix (filled with zeros).
 *
 * The algorithm is composed of two phases:
 *
 *   Phase 1: Row and Column reduction
 *     Step 1: subtract the minimum value of each row
 *              from the entries of that row
 *
 *     Step 2: subtract the minimum value of each column
 *              from the entries of that column
 *
 *
 *   Phase 2: Optimization of the problem
 *     Step 1: Draw a minimum number of lines to cover all the zeros of the matrix
 * a: starting from the first row, if there is exactly one zero in that row
 *    mark a square around that zero entry and draw a vertical line
 *    passing through it
 * b: if there are non-covered zeros:starting from the first column,
 *    if there is exactly one zero in that column mark a square around that
 *    zero entry and draw a horizontal line passing through it
 *
 *     Step 2: If there is the number of squared zeros if the same as
 *              the dimension of the matrix output the solution, otherwise continue
 *
 *     Step 3: Identify the minimum value of the undeleted (= uncrossed) cells
 * a: add the minimum to the intersection points of the present cost matrix
 * b: subtract the minimum from all the undeleted cells of the present cost matrix
 *
 *     Step 4: Go to step 1 again
*/

class Hungarian[T](source: List[T], target: List[T]){

  def display[T](matrix: List[List[T]]){
    for (row <- matrix){
      println(row.mkString(" "))
    }
  }

  /*
  * transforms the problem of finding a minimum solution into finding
  * a maximum solution
  */
  private def transformMaxIntoMin(costs: List[List[Int]]): List[List[Int]] = {
    val maxi = costs.flatten.max + 1
    costs.map(x => x.map(y => maxi - y))
  }

  /*
  * Reduction phase of the algorithm:
  *   subtract the minimim row value from each row
  *   subtract the minimum column value from each column
  */
  private def reductionPhase(costs: List[List[Int]]): List[List[Int]] = {
    // substract minimum from rows
    val rowSub = costs.map(row => {
      val mini = row.min
      row.map(c => c - mini)
    })

    // get minimum for each column
    val minCol = (0 to (costs.length - 1)).toList
        .map(j => rowSub.map(row => row.apply(j)))
          .map(col => col.min)

    // substract minimum from columns
    val colSub = rowSub.map(row => row.zip(minCol).map(tup => tup._1 - tup._2))
    colSub
  }

  /*
  * Covering part of phase 2: given a reduced cost matrix, finds the minimum
  * number of lines that can cover all the zeros.
  */

  private def covering(costs: List[List[Int]]): (List[(Int, Int)], List[Int], List[Int], List[(Int, Int)]) = {
    val indexes = (0 to costs.length - 1).toList

    val tmp = costs.map(row => row.zipWithIndex.filter(_._1 == 0).map(_._2))
    val zeroOccurences = tmp.zipWithIndex.map(tup => tup._1.map(el => (tup._2, el))).flatten

    var squares = List[(Int, Int)]()
    var rowLines = List[Int]()
    var colLines = List[Int]()
    var uncrossed = zeroOccurences
    var nbzeros = 1
    var crossed = List[(Int, Int)]()

    while(uncrossed.length > 0){
      val size = uncrossed.length

      //row scanning
      for(i <- indexes){
        val ua = uncrossed.filter(_._1 == i)
        if(ua.length == nbzeros){
          val s = ua(0)
          squares = s :: squares
          colLines = (colLines ++ List(s._2)).distinct
          rowLines = (rowLines ++ List(s._1)).distinct
          for(z <- uncrossed){
            if((z._1 == s._1 || z._2 == s._2 )){
              uncrossed = uncrossed.filterNot(_ == z)
              if(z != s) crossed = z :: crossed
            }
          }
        }
      }
      if(uncrossed.length == size){
        nbzeros += 1
      } else {
        nbzeros = 1
      }

    }
    (squares, rowLines, colLines, crossed)
  }

  /*
  * Determines whether the solution to the problem is complete or not
  */
  private def complete(squares: List[(Int, Int)], matLength: Int): Boolean = {
    for(i <- (0 to matLength - 1)){
      val row = squares.find(_._1 == i)
      val col = squares.find(_._2 == i)
      (row, col) match{
        case (Some(r), Some(c)) =>
        case _ => return false
      }

    }
    true
  }

  /*
  * Updates the cost matrix by finding the minimum value from uncovered cells,
  * adding it to intersection points and substracting it from uncovered cells.
  */
  private def updateCosts(costs: List[List[Int]], rowCross: List[Int], colCross: List[Int], squares: List[(Int, Int)], crossed: List[(Int, Int)]): List[List[Int]] = {

    val indexes = (0 to costs.length - 1).toList
    var same = false
    var marquedRow = indexes.filterNot(squares.map(_._1).toSet)
    var marquedCol = List[Int]()

    while (!same){
      var sizeR = marquedRow.length
      var sizeC = marquedCol.length
      marquedCol = (marquedCol ::: crossed.filter(c => marquedRow.contains(c._1)).map(_._2).distinct).distinct
      marquedRow = (marquedRow ::: squares.filter(s => marquedCol.contains(s._2)).map(_._1).distinct).distinct
      same = (sizeR == marquedRow.length && sizeC == marquedCol.length)
    }

    val unlinedRows = marquedRow
    val unlinedCols = indexes.filterNot(marquedCol.toSet)

    val zero = costs.zipWithIndex.map(ri => ri._1.zipWithIndex.filter(_._1 == 0).map(cj =>(ri._2, cj._2))).flatten
    val mini = unlinedRows.map(r => (unlinedCols.map(c => costs.apply(r).apply(c)))).flatten.min
    val newCosts = costs.zipWithIndex.map(row => {
      if (unlinedRows.contains(row._2)){
        row._1.zipWithIndex.map(col => {
          if (unlinedCols.contains(col._2)){
            col._1 - mini
          } else col._1

        })
      } else row._1.zipWithIndex.map(col => {
        if (!unlinedCols.contains(col._2)){
          col._1 + mini
        } else col._1

      })
    })
    newCosts
  }

  /*
  * Optimization phase of the problem:
  *   cover cost matrix with the minimum number of lines,
  *   if the solution is complete output it,
  *   otherwise reduce the cost matrix and repeat
  */
  private def optimizationPhase(costs: List[List[Int]]): List[(Int, Int)] = {
    val (squares, rows, cols, crossed) = covering(costs)
    if(!complete(squares, costs.length)) {
      val newCosts = updateCosts(costs, rows, cols, squares, crossed)
      optimizationPhase(newCosts)
    } else squares
  }

  /*
  * Computes the solution to the problem by applying the two phases
  */
  private def findSolution(costs: List[List[Int]]): List[(T, T)] = {
    val redMatrix = reductionPhase(costs)
    val positionSolution = optimizationPhase(redMatrix)
    positionSolution.map(rc => (source.apply(rc._1), target.apply(rc._2)))
  }

  /*
  * create a balances problem by transforming the cost matrix into a square one
  */
  private def balance(costs: List[List[Int]]): List[List[Int]] = {
    val diff = source.length - target.length

    if( diff == 0) costs
      else if(diff > 0) costs.map(_ ::: List.fill(diff)(0))
      else costs ::: List.fill(-diff)(List.fill(target.length)(0))
  }

  /*
  * Finds the solution to the assignment problem given the cost matrix
  */
  def solve(costs: List[List[Int]], findMax: Boolean): List[(T, T)] = {

    val costMat = if(findMax) transformMaxIntoMin(costs) else costs
    val finalCostMatrix = balance(costMat)
    findSolution(finalCostMatrix)
  }



  /*
  * Finds the solution to the assignment problem given a function
  * computing costs
  */
  def solve(fun: (T, T) => Int, findMax: Boolean, tostr: (T, T) => Boolean): List[(T, T)] = {
    // create the cost matrix from source, target and function
    val costsMatrix = source.map(s => target.map(t => fun(s, t)))
    solve(costsMatrix, findMax)
  }
}
