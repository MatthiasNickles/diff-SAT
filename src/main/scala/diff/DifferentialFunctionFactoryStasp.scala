/**
  * delSAT
  *
  * Copyright (c) 2018,2019 Matthias Nickles
  *
  * matthiasDOTnicklesATgmxDOTnet
  *
  * This code is licensed under MIT License (see file LICENSE for details)
  *
  */

package diff

import com.accelad.math.nilgiri.autodiff.DifferentialFunctionFactory
import com.accelad.math.nilgiri.{DoubleReal, DoubleRealFactory}

class DifferentialFunctionFactoryStasp extends DifferentialFunctionFactory[DoubleReal](DoubleRealFactory.instance()) { }