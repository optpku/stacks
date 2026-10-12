/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedAction
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Quotient
public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived completion from ideal-power quotient towers

This leaf owns the canonical maps from a derived module to the quotient-tensor stages and the
property that a morphism presents the corresponding derived-limit comparison.  Over a Noetherian
ring, a functor equipped with these comparisons is a left adjoint to the inclusion of
derived-complete objects.

@stack 0922
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IdealPower

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/-- The quotient map from the regular degree-zero module to the `n`th positive ideal-power
quotient stage. -/
@[stacks 0922 "regular module to an ideal-power quotient stage"]
abbrev quotientMap (I : Ideal A) (n : ℕ) :
    ModuleCat.single0 (ModuleCat.of A A) ⟶ stage I n :=
  ModuleCat.single0Functor.map
    (ModuleCat.ofHom
      (Submodule.mkQ ((I ^ (n + 1)) • (⊤ : Submodule A A))))

/-- The canonical map from `K` to the `n`th stage
`(A ⧸ I ^ (n + 1))[0] ⊗ᴸ K` of the ideal-power quotient tensor tower. -/
@[stacks 0922 "derived ideal-power completion stage map"]
noncomputable def toStage (I : Ideal A) (K : DMod) (n : ℕ) :
    K ⟶ (tensorSystem I K).obj (op n) :=
  (ModuleCat.DerivedAction.fixedRightActionIso K).inv ≫
    (derivedTensorProduct K).map (quotientMap I n)

/-- The canonical maps to ideal-power quotient tensor stages are compatible with successor
transitions in the inverse system. -/
@[stacks 0922 "compatibility of ideal-power completion stage maps"]
theorem toStage_comp_stepMap (I : Ideal A) (K : DMod) (n : ℕ) :
    toStage I K (n + 1) ≫ (tensorSystem I K).stepMap n = toStage I K n := sorry
-- Proof strategy: unfold `toStage` and `stepMap`, use naturality of the fixed-right action
-- comparison, and reduce to compatibility of successive quotient maps.

/-- A morphism is the canonical comparison to the derived limit of the ideal-power quotient
tensor tower when its composites with all stage projections are the maps `toStage`. -/
@[stacks 0922 "derived ideal-power completion comparison"]
def IsCompletionComparison (I : Ideal A) (K L : DMod) (c : K ⟶ L) : Prop :=
  ∃ h : IsDerivedLimit (tensorSystem I K) L,
    ∀ n : ℕ, c ≫ h.stageProjection n = toStage I K n

/-- The defining specification of an ideal-power derived-completion comparison. -/
@[stacks 0922 "derived ideal-power completion comparison specification"]
theorem isCompletionComparison_iff (I : Ideal A) (K L : DMod) (c : K ⟶ L) :
    IsCompletionComparison I K L c ↔
      ∃ h : IsDerivedLimit (tensorSystem I K) L,
        ∀ n : ℕ, c ≫ h.stageProjection n = toStage I K n := sorry
-- Proof strategy: unfold `IsCompletionComparison`; the statement is its public specification.

/-- The derived-limit witness selected from a quotient-tower completion comparison. -/
@[stacks 0922 "derived-limit witness from an ideal-power completion comparison"]
noncomputable def IsCompletionComparison.isDerivedLimit
    {I : Ideal A} {K L : DMod} {c : K ⟶ L}
    (hc : IsCompletionComparison I K L c) :
    IsDerivedLimit (tensorSystem I K) L :=
  Classical.choose hc

/-- The selected derived-limit witness recovers every canonical ideal-power stage map. -/
@[stacks 0922 "stage formula for an ideal-power completion comparison"]
theorem IsCompletionComparison.comp_stageProjection
    {I : Ideal A} {K L : DMod} {c : K ⟶ L}
    (hc : IsCompletionComparison I K L c) (n : ℕ) :
    c ≫ hc.isDerivedLimit.stageProjection n = toStage I K n := sorry
-- Proof strategy: unfold `IsCompletionComparison.isDerivedLimit` and apply the second
-- projection of the witness selected from `hc`.

/-- Over a Noetherian ring, an ideal-power derived-completion comparison is invertible exactly
when its source is derived complete with respect to the ideal. -/
@[stacks 0922 "derived-complete criterion for ideal-power completion"]
theorem isDerivedComplete_iff_isIso
    [IsNoetherianRing A] (I : Ideal A) {K L : DMod} (c : K ⟶ L)
    (hc : IsCompletionComparison I K L c) :
    K.IsDerivedCompleteWithRespectTo I ↔ IsIso c := sorry
-- Proof strategy: use the Noetherian powered-Koszul pro-isomorphism to identify `hc` with
-- the canonical derived-completion unit, then apply the reflector fixed-point criterion.

/-- Proposition 15.95.2: over a Noetherian ring, a functor whose unit components are the
canonical ideal-power quotient-tower completion comparisons is left adjoint to the inclusion of
derived-complete objects. -/
@[stacks 0922]
theorem completionFunctor_isLeftAdjoint
    [IsNoetherianRing A] (I : Ideal A)
    (L : DMod ⥤ (_root_.DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η : 𝟭 DMod ⟶ L ⋙ (_root_.DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη : ∀ K : DMod, IsCompletionComparison I K (L.obj K).obj (η.app K)) :
    L.IsLeftAdjoint := sorry
-- Proof strategy: show that `η.app K` is initial among maps from `K` to a derived-complete
-- object using `isDerivedComplete_iff_isIso`, and assemble the resulting universal arrows
-- into the standard left-adjoint criterion.

end CategoryTheory.DerivedCategory.IdealPower
