module

public import ReasLib.CategoryTheory.Sites.Precoverage.QuasiContinuous
public import StacksCheckRecall.CommandCrossRef

/-!
# Remark 7.13.6

Quasi-continuity belongs to selected precoverages, so its reusable owner is
`CategoryTheory.Functor.Precoverage.IsQuasiContinuous` rather than a saturated
topology-level wrapper.
-/

@[expose] public section

/- Remark 7.13.6 (00WZ): a quasi-continuous functor sends selected covers to
tautologically equivalent selected covers and preserves the relevant pullback
comparisons; it consequently induces continuity for generated topologies. -/
@[stacks 00WZ "definition"] #check @CategoryTheory.Functor.Precoverage.IsQuasiContinuous

@[stacks 00WZ "cover image"] #check @CategoryTheory.Functor.Precoverage.IsQuasiContinuous.map_mem

@[stacks 00WZ "site continuity"]
#check @CategoryTheory.Functor.Precoverage.IsQuasiContinuous.toIsContinuous

@[stacks 00WZ "topology continuity"] #check @CategoryTheory.Functor.Precoverage.IsQuasiContinuous.toContinuous
