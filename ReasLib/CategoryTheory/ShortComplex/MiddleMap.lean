/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Strictification of the middle map of a short-complex morphism

The property in this file is independent of homological complexes and of the particular functor
used to pass to a homotopy or localization category.  It records exactly the source-facing
question: can a prescribed middle map be replaced by the middle component of a strict short-complex
morphism without changing its image under a functor?
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.ShortComplex

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D]

/-- A prescribed middle map is strictifiable along `F` when it is the image of the middle component
of a strict short-complex morphism with the prescribed outer components. -/
@[stacks 014J "middle-map strictifiability predicate"]
def IsMiddleMapStrictifiable (F : C ⥤ D) (S T : ShortComplex C)
    (a : S.X₁ ⟶ T.X₁) (b : S.X₂ ⟶ T.X₂) (c : S.X₃ ⟶ T.X₃) : Prop :=
  ∃ φ : S ⟶ T, φ.τ₁ = a ∧ φ.τ₃ = c ∧ F.map φ.τ₂ = F.map b

/-- Strictly commuting outer squares make the prescribed middle map strictifiable. -/
@[stacks 014J "strict squares give middle-map strictifiability"]
theorem isMiddleMapStrictifiable_of_commSq
    (F : C ⥤ D) {S T : ShortComplex C}
    {a : S.X₁ ⟶ T.X₁} {b : S.X₂ ⟶ T.X₂} {c : S.X₃ ⟶ T.X₃}
    (h₁₂ : CommSq S.f a b T.f) (h₂₃ : CommSq S.g b c T.g) :
    IsMiddleMapStrictifiable F S T a b c := sorry

/-- The predicate unfolds to a strict short-complex morphism with fixed outer components and a
functorial equality for the middle component. -/
@[simp]
theorem isMiddleMapStrictifiable_iff
    (F : C ⥤ D) (S T : ShortComplex C)
    (a : S.X₁ ⟶ T.X₁) (b : S.X₂ ⟶ T.X₂) (c : S.X₃ ⟶ T.X₃) :
    IsMiddleMapStrictifiable F S T a b c ↔
      ∃ φ : S ⟶ T, φ.τ₁ = a ∧ φ.τ₃ = c ∧ F.map φ.τ₂ = F.map b := sorry

end CategoryTheory.ShortComplex
