module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle
public import ReasLib.CategoryTheory.InverseSystem.Milnor.ShortExact.Snake
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Milnor consequences for short exact systems of modules

This leaf exposes the module-valued form of the standard Milnor consequence: if the left term of
a short exact sequential row is Mittag-Leffler, the induced map on canonical first derived
limits is an isomorphism.
@stack 0H31
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.ShortExact

variable {R : Type u} [Ring R]

/-- In a short exact row of sequential modules with Mittag-Leffler left term, the map from the
middle to the right canonical first derived limit is an isomorphism. -/
@[stacks 0H31 "first derived limit after a Mittag-Leffler term"]
theorem firstDerivedLimitMap_isIso
    {S : ShortComplex (SequentialInverseSystem (ModuleCat.{u} R))}
    (hS : S.ShortExact) (hX₁ : S.X₁.IsMittagLeffler) :
    IsIso (SequentialInverseSystem.firstDerivedLimitMap S.g) := sorry

/-- The isomorphism on canonical first derived limits induced by the right map of a short exact
row with Mittag-Leffler left term. -/
@[stacks 0H31 "first derived limit isomorphism after a Mittag-Leffler term"]
noncomputable def firstDerivedLimitIso
    {S : ShortComplex (SequentialInverseSystem (ModuleCat.{u} R))}
    (hS : S.ShortExact) (hX₁ : S.X₁.IsMittagLeffler) :
    S.X₂.firstDerivedLimit ≅ S.X₃.firstDerivedLimit :=
  letI := firstDerivedLimitMap_isIso hS hX₁
  asIso (SequentialInverseSystem.firstDerivedLimitMap S.g)

end CategoryTheory.ModuleCat.ShortExact
