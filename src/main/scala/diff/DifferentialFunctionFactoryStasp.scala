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

import com.accelad.math.nilgiri.autodiff.DifferentialFunctionFactory
import com.accelad.math.nilgiri.{DoubleReal, DoubleRealFactory}

class DifferentialFunctionFactoryStasp extends DifferentialFunctionFactory[DoubleReal](DoubleRealFactory.instance()) { }