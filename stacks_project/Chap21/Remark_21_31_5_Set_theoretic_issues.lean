module

public import ReasLib.Topology.Category.LCCat.SmallStage
import StacksCheckRecall

@[expose] public section

universe u w

open CategoryTheory
open LCCat.SmallStage

/- Remark 21.31.5 (09X2): the category `LCCat` and its qc coverings are large.  For a set-sized
initial family `S₀`, a set-theoretic replacement argument chooses a small stage `LC_α` containing
`S₀`, closed under all countable limits and colimits which exist in `LCCat`, and satisfying the
chosen cardinal bound `Bound`.  The textbook's representative set `Cov` is represented here by
the concrete canonical precoverage `qcPrecoverage P := LCCat.qcPrecoverage.comap P.ι`; under
pullback closure it gives `qcPretopology P` and `qcTopology P`, so no site data is hidden behind an
existential package. -/
@[stacks 09X2]
#check @LCCat.SmallStage.exists_containing

/- The set-theoretic replacement hypothesis is explicit in the reusable owner. -/
#check @LCCat.SmallStage.IsReplacementBound

/- Closure and bounded-size clauses are reusable object-property predicates. -/
#check @LCCat.SmallStage.IsClosedUnderCountableLimits
#check @LCCat.SmallStage.IsClosedUnderCountableColimits
#check @LCCat.SmallStage.IsClosedUnderBoundedSize

/- A chosen stage carries concrete property data; its site is canonically derived. -/
#check @LCCat.SmallStage
#check @LCCat.SmallStage.qcPrecoverage
#check @LCCat.SmallStage.qcPretopology
#check @LCCat.SmallStage.qcTopology
#check @LCCat.SmallStage.qcPrecoverageOf
#check @LCCat.SmallStage.qcPretopologyOf
#check @LCCat.SmallStage.qcTopologyOf

/- Family presentations and the stage-level qc criterion remain available to downstream proofs. -/
#check @LCCat.SmallStage.toAmbient
#check @LCCat.SmallStage.toAmbient_toPresieve
#check @LCCat.SmallStage.mem_qcPrecoverage_iff
#check @LCCat.SmallStage.isCovering_qcPrecoverage_iff

end
