module

public import ReasLib.CategoryTheory.Filtration.Complex.StageSequence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of filtration-stage sequence inclusions

The objectwise maps from a selected sequence of filtration stages to the underlying complex form
a natural transformation in the filtered complex.  Bundling them here lets downstream functorial
constructions whisker or map the whole comparison directly.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.FilteredComplex.StageSequence

variable {C : Type u} [CategoryTheory.Category.{v} C]
  [CategoryTheory.Limits.HasZeroMorphisms C]

/-- The selected stage inclusions, natural in the filtered complex. -/
@[stacks 0D8Z "natural transformation from selected filtration stages to the underlying complex"]
noncomputable def toUnderlyingNatTrans (p : ℕ → ℤ) (hp : Antitone p) :
    functor (C := C) p hp ⟶ underlyingFunctor ⋙ (Functor.const ℕ) where
  app K := toUnderlying K p hp
  naturality _ _ f := map_comp_toUnderlying f p hp

/-- A component of `toUnderlyingNatTrans` is the canonical transformation from the selected
stage sequence to the constant underlying complex. -/
@[simp, stacks 0D8Z "component of the selected-stage inclusion natural transformation"]
theorem toUnderlyingNatTrans_app (p : ℕ → ℤ) (hp : Antitone p) (K : FilteredComplex C) :
    (toUnderlyingNatTrans p hp).app K = toUnderlying K p hp := sorry

/-- Evaluating `toUnderlyingNatTrans` at a filtered complex and a sequence index gives the
corresponding filtration-stage inclusion. -/
@[simp, stacks 0D8Z "component at an index of the selected-stage inclusion natural transformation"]
theorem toUnderlyingNatTrans_app_app (p : ℕ → ℤ) (hp : Antitone p)
    (K : FilteredComplex C) (n : ℕ) :
    ((toUnderlyingNatTrans p hp).app K).app n = K.stageInclusion (p n) := sorry

end CategoryTheory.FilteredComplex.StageSequence
