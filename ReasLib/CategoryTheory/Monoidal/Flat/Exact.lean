/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import ReasLib.CategoryTheory.Monoidal.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact sequences and flat objects in monoidal abelian categories

The flatness lemmas needed for module presheaves and module sheaves are categorical.  Their
natural setting is an abelian monoidal category with additive tensor, right-exact fixed-factor
tensor functors, and enough flat objects.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

/-- Exactness data for a right-augmented sequence
`⋯ ⟶ F 2 ⟶ F 1 ⟶ F 0 ⟶ Q ⟶ 0`. -/
@[stacks 03EZ "right-augmented exactness"]
structure RightAugmentedExact
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (F : ℕ → C) (d : ∀ n, F (n + 1) ⟶ F n)
    (Q : C) (q : F 0 ⟶ Q) : Prop where
  /-- Consecutive differentials compose to zero. -/
  d_comp_d : ∀ n, d (n + 1) ≫ d n = 0
  /-- The last differential composes trivially with the augmentation. -/
  d_comp_q : d 0 ≫ q = 0
  /-- The sequence is exact at every positive-resolution term. -/
  exact_succ : ∀ n,
    (ShortComplex.mk (d (n + 1)) (d n) (d_comp_d n)).Exact
  /-- The sequence is exact at the degree-zero resolution term. -/
  exact_zero : (ShortComplex.mk (d 0) q d_comp_q).Exact
  /-- The augmentation is an epimorphism. -/
  epi_q : Epi q

namespace MonoidalCategory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [EnoughFlatObjects C]
variable [∀ X : C, PreservesFiniteColimits (tensorRight X)]

/-- If the quotient in a short exact sequence is flat, tensoring that sequence on the right by
an arbitrary object preserves short exactness. -/
@[stacks 03EX]
theorem shortExact_map_tensorRight_of_flat_quotient
    [BraidedCategory C]
    (S : ShortComplex C) (hS : S.ShortExact) (G : C) [IsFlat S.X₃] :
    (S.map (tensorRight G)).ShortExact := sorry

/-- If the quotient in a short exact sequence is flat, tensoring on the left by an arbitrary
object preserves short exactness in a braided monoidal category. -/
@[stacks 03EX "braided left-tensor form"]
theorem shortExact_map_tensorLeft_of_flat_quotient
    [BraidedCategory C]
    (S : ShortComplex C) (hS : S.ShortExact) (G : C) [IsFlat S.X₃] :
    (S.map (tensorLeft G)).ShortExact := sorry

/-- In a short exact sequence with flat quotient, the left term is flat exactly when the middle
term is flat. -/
@[stacks 03EY]
theorem isFlat_left_iff_middle_of_shortExact
    (S : ShortComplex C) (hS : S.ShortExact) [IsFlat S.X₃] :
    IsFlat S.X₁ ↔ IsFlat S.X₂ := sorry

end MonoidalCategory

namespace RightAugmentedExact

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [EnoughFlatObjects C]
variable [∀ X : C, PreservesFiniteColimits (tensorRight X)]

/-- Tensoring an exact right-augmented sequence of flat objects by an arbitrary object preserves
right-augmented exactness. -/
@[stacks 03EZ]
theorem map_tensorRight
    [BraidedCategory C]
    {F : ℕ → C} {d : ∀ n, F (n + 1) ⟶ F n}
    {Q : C} {q : F 0 ⟶ Q}
    (h : RightAugmentedExact F d Q q) (G : C)
    [IsFlat Q] [∀ n, IsFlat (F n)] :
    RightAugmentedExact
      (fun n ↦ (tensorRight G).obj (F n))
      (fun n ↦ (tensorRight G).map (d n))
      ((tensorRight G).obj Q) ((tensorRight G).map q) := sorry

end RightAugmentedExact

namespace ShortComplex

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]
variable [∀ X : C, PreservesFiniteColimits (tensorRight X)]

/-- If all three terms of a short complex are flat and tensoring the complex by every object is
exact at its middle term, then the cokernel of its second map is flat. -/
@[stacks 08G0 "abstract short-complex criterion"]
theorem isFlat_cokernel_g
    (S : ShortComplex C) [IsFlat S.X₁] [IsFlat S.X₂] [IsFlat S.X₃]
    (hExact : ∀ G : C, (S.map (tensorRight G)).Exact) :
    IsFlat (cokernel S.g) := sorry

end ShortComplex

end CategoryTheory
