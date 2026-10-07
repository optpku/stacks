module

public import ReasLib.Algebra.Module.Torsion.FlatBaseChange
import StacksCheckRecall

/-!
# Lemma 15.22.4

@stack 0AXM
-/

universe u v w

open scoped TensorProduct

/- Lemma 15.22.4 (0AXM): a flat map of domains preserves torsion-freeness after tensor base
change. The library-facing tensor orientation is `R' ⊗[R] M`. -/
@[stacks 0AXM]
#check fun {R : Type u} {R' : Type v} {M : Type w}
    [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']
    [Module.Flat R R'] [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] ↦
  (Module.IsTorsionFree.baseChange_of_flat (R := R) (R' := R') (M := M) :
    Module.IsTorsionFree R' (R' ⊗[R] M))

#check @Module.IsTorsionFree.baseChange_of_flat
