/**
 * DelSAT
 *
 *  A tool for differentiable satisfiability and differentiable answer set programming
 *
 * Copyright (c) 2018 Matthias Nickles
 *
 * THIS CODE IS PROVIDED AS IS, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED.
 *
 */

package diff;

import com.accelad.math.nilgiri.DoubleReal;
import com.accelad.math.nilgiri.autodiff.DifferentialFunction;

import java.io.Serializable;

public class UncertainAtomsSeprt implements Serializable {  // for interoperability reasons, this is a Java class.
    // Also see same class in prasp2.

    public String parameterAtomsSeq[];

    public String measuredAtomsSeq[];

    public DifferentialFunction<DoubleReal> innerCostExpressionInstances[];

    public String costFunAsPredicate; // null or an unary predicate with #c as argument

    public UncertainAtomsSeprt(String parameterAtomsSeq[], String measuredAtomsSeq[], DifferentialFunction<DoubleReal> innerCostExpressionInstances[],
                               String costFunAsPredicate) {

        this.parameterAtomsSeq = parameterAtomsSeq;

        this.measuredAtomsSeq = measuredAtomsSeq;

        this.innerCostExpressionInstances = innerCostExpressionInstances;

        this.costFunAsPredicate = costFunAsPredicate;

    }

}

