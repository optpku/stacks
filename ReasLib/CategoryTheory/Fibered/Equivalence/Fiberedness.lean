module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.Equivalence.StronglyCartesian

/-!
# Fibredness under equivalence over a base

This module records invariance of `Functor.IsFibered` under equivalence over the base, both for
possibly universe-changing based functors and for equivalences in a fixed `BasedCategory`.
-/

@[expose] public section

universe v u vX uX vY uY vS uS

namespace CategoryTheory

open Functor
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace BasedFunctor.IsEquivalence

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- If `F : X ⥤ᵇ Y` is an equivalence over `C`, then `X` is fibred over `C` if and
only if `Y` is fibred over `C`. -/
theorem isFibered_iff (F : X ⥤ᵇ Y) [F.IsEquivalence] :
    X.p.IsFibered ↔ Y.p.IsFibered := sorry
/- Proof strategy: rewrite fibredness on both sides with
`Functor.IsFibered.iff_exists_isStronglyCartesian`. For the forward implication, choose
`e := F.asQuasiInverse`; lift a target base arrow at `e.inverse.obj y` in `X`, map that lift with
`BasedFunctor.IsEquivalence.isStronglyCartesian_map`, and postcompose with the vertical isomorphism
`e.counitIso.hom.app y` to obtain a strongly cartesian arrow with codomain `y`. For the reverse
implication, apply the same construction to `e.inverse` using `e.symm.isEquivalence`; its counit is
the original unit with reversed orientation. The based unit and counit components lie over
identities, so composition preserves the required displayed base arrow. -/

end BasedFunctor.IsEquivalence

namespace BasedCategory.Equivalence

variable {X Y : BasedCategory.{vS, uS} C}

/-- Fibredness is invariant under equivalence in the bicategory `BasedCategory C`. -/
@[stacks 042G "fibredness invariant under equivalence over a base"]
theorem isFibered_iff (e : X ≌ Y) :
    X.p.IsFibered ↔ Y.p.IsFibered := sorry
/- Proof strategy: apply `BasedCategory.Equivalence.isStronglyCartesian_map` to `e` in one
direction and to `e.symm` in the other, using the existence characterization of fibredness by
strongly cartesian lifts. -/

end BasedCategory.Equivalence

end CategoryTheory
