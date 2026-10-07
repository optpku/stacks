module

public import stacks_project.Chap64.«64_16_1_1»
public import stacks_project.Chap64.Theorem_64_14_4_Weil
import StacksCheckRecall

open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Curve

/- Remark 64.16.3: even though the argument of
`lefschetzTraceFormula_compactSupport` consists of reductions and mostly
algebra, that compact-support trace formula (Theorem 64.16.1) is much
stronger than Weil's geometric trace formula `weilTraceFormula`
(Theorem 64.14.4) because its coefficient input is `K` in
`EtaleConstructibleTorFinite`, not merely constant coefficients. -/
@[stacks 03UJ] #check lefschetzTraceFormula_compactSupport
@[stacks 03UJ] #check weilTraceFormula
