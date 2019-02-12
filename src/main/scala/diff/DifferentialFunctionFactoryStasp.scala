/**
  * delSAT
  *
  * Copyright (c) 2018, 2019 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * License: https://github.com/MatthiasNickles/delSAT/blob/master/LICENSE
  *
  */

package diff

import com.accelad.math.nilgiri.autodiff.{AbstractUnaryFunction, DifferentialFunction, DifferentialFunctionFactory, Variable}
import com.accelad.math.nilgiri.{DoubleReal, DoubleRealFactory}

class DifferentialFunctionFactoryStasp extends DifferentialFunctionFactory[DoubleReal](DoubleRealFactory.instance()) {

  class SCAbstractUnaryFunction(iX: DifferentialFunction[DoubleReal]) extends AbstractUnaryFunction[DoubleReal](iX: DifferentialFunction[DoubleReal]) {

    override def getValue: DoubleReal = new DoubleReal(getReal) //rNFactory.phi(arg().getValue())

    override def getReal: Double = {

      assert(false, "differential function phi() should not be called from prasp2")

      val uncertainAtomIndex = arg().getReal.toInt // must be toAbsEli positive Eli

      -1d // dummy

    }

    @deprecated override def diff(i_v: Variable[DoubleReal]): DifferentialFunction[DoubleReal] = { // subject to removal in one of the next versions of DelSAT

      //prt("Diff phi wrt " + i_v + "...")

      if (i_v.getName.stripPrefix("anyPwPrForAtom_").toDouble == arg().getValue().getReal)

      // We are returning the partial derivative d/dx, where x = i_v is toAbsEli variable with name "anyPwPrForAtom_"+uai, with uai being the index
      // of an uncertain atom ua. Since phi(uai) is defined as sum(probabilities of all pws where atom ua holds), the result is
      // either 1 (if this sum is differentiated against the probability variable of any possible world where atom ua holds) or 0 (otherwise).

        one

      else

        zero

    }

    override def toString: String = "phi(" + arg.toString + ")"

    override def getFormula(variables: java.util.List[Variable[DoubleReal]]): String = "phi(" + arg.getFormula(variables) + ")"

  }

  def phi(iX /*index of a measured atom (not an eli(!), since we don't have elis yet when this function is generated)*/ :
          DifferentialFunction[DoubleReal]) = new SCAbstractUnaryFunction(iX)

}