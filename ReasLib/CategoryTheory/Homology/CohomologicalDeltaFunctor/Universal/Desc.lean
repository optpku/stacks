/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Universal Extension of Degree-Zero Transformations

A universal cohomological delta functor has a canonical chosen extension of
every degree-zero natural transformation.  The choice is exposed only through
its specification and uniqueness API.
-/

noncomputable section

universe vA uA vB uB

namespace CategoryTheory.CohomologicalDeltaFunctor.IsUniversal

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]

/-- The chosen extension of a degree-zero natural transformation out of a
universal cohomological delta functor. -/
@[stacks 010S "universal extension of a degree-zero transformation"]
noncomputable def desc {F G : CohomologicalDeltaFunctor A B} [IsUniversal F]
    (t : (F.F 0).obj ⟶ (G.F 0).obj) : Hom F G :=
  Classical.choose (IsUniversal.existsUnique_hom G t)

/-- The degree-zero component of the chosen universal extension is the given
natural transformation. -/
@[simp]
theorem desc_app_zero {F G : CohomologicalDeltaFunctor A B} [IsUniversal F]
    (t : (F.F 0).obj ⟶ (G.F 0).obj) :
    (desc t).app 0 = t := sorry

/-- Any extension with the prescribed degree-zero component is the chosen
universal extension. -/
theorem desc_unique {F G : CohomologicalDeltaFunctor A B} [IsUniversal F]
    (t : (F.F 0).obj ⟶ (G.F 0).obj) (τ : Hom F G)
    (hτ : τ.app 0 = t) :
    τ = desc t := sorry

/-- Extending the degree-zero component of an existing delta-functor
morphism recovers that morphism. -/
@[simp]
theorem desc_of_app {F G : CohomologicalDeltaFunctor A B} [IsUniversal F]
    (τ : Hom F G) :
    desc (τ.app 0) = τ := sorry

/-- The universal extension of the identity degree-zero transformation is
the identity delta-functor morphism. -/
@[simp]
theorem desc_id (F : CohomologicalDeltaFunctor A B) [IsUniversal F] :
    desc (𝟙 ((F.F 0).obj)) = Hom.id F := sorry

/-- Universal extension commutes with postcomposition by a delta-functor
morphism. -/
@[simp]
theorem desc_comp {F G H : CohomologicalDeltaFunctor A B} [IsUniversal F]
    (t : (F.F 0).obj ⟶ (G.F 0).obj) (σ : Hom G H) :
    desc (t ≫ σ.app 0) = Hom.comp (desc t) σ := sorry

end CategoryTheory.CohomologicalDeltaFunctor.IsUniversal
