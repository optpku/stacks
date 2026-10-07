module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Uniqueness of Sequential Derived Limits

This leaf records the stagewise uniqueness principle for Milnor models of a
sequential derived limit. It is independent of a particular derived category,
truncation convention, or source application.
@stack 08U5
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.IsDerivedLimit

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Stacks 08TC: any two derived limits of a sequential inverse system are
isomorphic by an isomorphism commuting with every canonical stage projection. -/
@[stacks 08TC, stacks 08U5]
theorem existsIsoOverStages {Ksys : SequentialInverseSystem D} {L L' : D}
    (h : IsDerivedLimit Ksys L) (h' : IsDerivedLimit Ksys L') :
    ∃ e : L ≅ L', ∀ n : ℕ, e.hom ≫ h'.stageProjection n = h.stageProjection n := sorry

end CategoryTheory.IsDerivedLimit
