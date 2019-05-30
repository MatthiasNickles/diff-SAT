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

package diff;

import com.accelad.math.nilgiri.DoubleReal;
import com.accelad.math.nilgiri.autodiff.DifferentialFunction;
import com.accelad.math.nilgiri.autodiff.Variable;
import scala.Int;

import java.io.Serializable;

public class UncertainAtomsSeprt implements Serializable {  // for interoperability reasons, this is a Java class.
    // Also see same class in prasp2.

    public String parameterAtomsSeq[];

    public String measuredAtomsSeq[];

    public DifferentialFunction<DoubleReal> innerCostExpressionInstances[];

    public scala.collection.mutable.HashMap<Int, Variable<DoubleReal>> eliToVariableInCostFunctions;

    //public String costFunAsPredicate; // null or an unary predicate with #c as argument

    public UncertainAtomsSeprt(String parameterAtomsSeq[], String measuredAtomsSeq[], DifferentialFunction<DoubleReal> innerCostExpressionInstances[],
                               scala.collection.mutable.HashMap<Int, Variable<DoubleReal>> eliToVariableInCostFunctions) {

        this.parameterAtomsSeq = parameterAtomsSeq;

        this.measuredAtomsSeq = measuredAtomsSeq;

        this.innerCostExpressionInstances = innerCostExpressionInstances;

        this.eliToVariableInCostFunctions = eliToVariableInCostFunctions;

    }

}

