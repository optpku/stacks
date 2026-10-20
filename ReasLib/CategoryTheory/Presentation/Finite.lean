/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentations from a family of generators

These object properties isolate two common categorical presentation patterns: a coequalizer of a
parallel pair between finite coproducts, and a cokernel of one map between finite coproducts.  The
generators are supplied by a functor and restricted by a property on its source.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u₂ v₂ u₁ v₁

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- Objects admitting a coequalizer presentation whose two terms are finite coproducts of
selected values of `G`. -/
@[stacks 09Y7]
def finiteCoequalizerPresentation [HasFiniteCoproducts D] [HasCoequalizers D]
    (G : C ⥤ D) (B : Set C) : ObjectProperty D :=
  fun X ↦
    ∃ (m n : ℕ) (V : Fin m → C) (U : Fin n → C),
      (∀ j, V j ∈ B) ∧ (∀ i, U i ∈ B) ∧
        ∃ (p q : (∐ fun j ↦ G.obj (V j)) ⟶ (∐ fun i ↦ G.obj (U i))),
          Nonempty (coequalizer p q ≅ X)

/-- Objects admitting a cokernel presentation whose two terms are finite coproducts of selected
values of `G`. -/
@[stacks 093D]
def finiteCokernelPresentation [Preadditive D] [HasFiniteCoproducts D] [HasCokernels D]
    (G : C ⥤ D) (B : Set C) : ObjectProperty D :=
  fun X ↦
    ∃ (m n : ℕ) (V : Fin m → C) (U : Fin n → C),
      (∀ j, V j ∈ B) ∧ (∀ i, U i ∈ B) ∧
        ∃ f : (∐ fun j ↦ G.obj (V j)) ⟶ (∐ fun i ↦ G.obj (U i)),
          Nonempty (cokernel f ≅ X)

/-- Finite coequalizer presentations are invariant under isomorphism of the presented object. -/
instance finiteCoequalizerPresentation_isClosedUnderIsomorphisms
    [HasFiniteCoproducts D] [HasCoequalizers D] (G : C ⥤ D) (B : Set C) :
    ObjectProperty.IsClosedUnderIsomorphisms (G.finiteCoequalizerPresentation B) := sorry

/-- Finite cokernel presentations are invariant under isomorphism of the presented object. -/
instance finiteCokernelPresentation_isClosedUnderIsomorphisms
    [Preadditive D] [HasFiniteCoproducts D] [HasCokernels D]
    (G : C ⥤ D) (B : Set C) :
    ObjectProperty.IsClosedUnderIsomorphisms (G.finiteCokernelPresentation B) := sorry

namespace FiniteCokernelPresentation

/-- The generator-kernel condition for a finite cokernel presentation: kernels of all maps
between finite coproducts of selected generators again admit such a presentation. -/
@[stacks 093H "generator-kernel condition"]
def HasKernels [Preadditive D] [HasFiniteCoproducts D] [HasKernels D] [HasCokernels D]
    (G : C ⥤ D) (B : Set C) : Prop :=
  ∀ (m n : ℕ) (V : Fin m → C) (U : Fin n → C),
    (∀ j, V j ∈ B) → (∀ i, U i ∈ B) →
      ∀ f : (∐ fun j ↦ G.obj (V j)) ⟶ (∐ fun i ↦ G.obj (U i)),
        G.finiteCokernelPresentation B (kernel f)

end FiniteCokernelPresentation

end CategoryTheory.Functor
