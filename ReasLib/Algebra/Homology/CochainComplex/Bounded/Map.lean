module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded cochain complexes and functors

This file records that a functor preserving zero morphisms sends bounded-below,
bounded-above, and bounded cochain complexes to complexes with the same bounds.
@stack 0E1U
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CochainComplex

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]

/-- Stacks `0E1U`: a functor preserving zero morphisms sends a bounded-below cochain complex to a
bounded-below cochain complex. -/
@[stacks 0E1U "functorial bounded-below support"]
theorem plus_map (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {K : CochainComplex C ℤ} (hK : CochainComplex.plus C K) :
    CochainComplex.plus D ((F.mapHomologicalComplex (up ℤ)).obj K) := sorry

/-- Stacks `0E1U`: a functor preserving zero morphisms sends a bounded-above cochain complex to a
bounded-above cochain complex. -/
@[stacks 0E1U "functorial bounded-above support"]
theorem minus_map (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {K : CochainComplex C ℤ} (hK : CochainComplex.minus C K) :
    CochainComplex.minus D ((F.mapHomologicalComplex (up ℤ)).obj K) := sorry

/-- Stacks `0E1U`: a functor preserving zero morphisms sends a bounded cochain complex to a bounded
cochain complex. -/
@[stacks 0E1U "functorial bounded support"]
theorem bounded_map (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {K : CochainComplex C ℤ} (hK : CochainComplex.bounded C K) :
    CochainComplex.bounded D ((F.mapHomologicalComplex (up ℤ)).obj K) := sorry

end CochainComplex
