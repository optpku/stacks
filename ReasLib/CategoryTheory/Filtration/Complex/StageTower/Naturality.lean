module

public import ReasLib.CategoryTheory.Filtration.Complex.StageTower
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of filtration-stage tower inclusions

The inclusions from the integer filtration-stage tower to the underlying complex are natural in
the filtered complex.  This leaf bundles the existing objectwise comparison as a transformation
between functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.StageTower

variable {C : Type u} [CategoryTheory.Category.{v} C]
  [CategoryTheory.Limits.HasZeroMorphisms C]

/-- The integer stage-tower inclusions, natural in the filtered complex. -/
@[stacks 012L "natural transformation from the integer stage tower to the underlying complex"]
noncomputable def toUnderlyingNatTrans :
    functor (C := C) ⟶ underlyingFunctor ⋙ (Functor.const ℤᵒᵖ) where
  app K := toUnderlying K
  naturality _ _ f := map_comp_toUnderlying f

/-- A component of `toUnderlyingNatTrans` is the canonical transformation from the integer
stage tower to the constant underlying complex. -/
@[simp, stacks 012L "component of the integer stage-tower inclusion natural transformation"]
theorem toUnderlyingNatTrans_app (K : FilteredComplex C) :
    (toUnderlyingNatTrans (C := C)).app K = toUnderlying K := sorry

/-- Evaluating `toUnderlyingNatTrans` at a filtered complex and an integer stage gives the
corresponding filtration-stage inclusion. -/
@[simp, stacks 012L "component at an index of the integer stage-tower inclusion natural transformation"]
theorem toUnderlyingNatTrans_app_app (K : FilteredComplex C) (i : ℤᵒᵖ) :
    ((toUnderlyingNatTrans (C := C)).app K).app i = K.stageInclusion i.unop := sorry

end CategoryTheory.FilteredComplex.StageTower
