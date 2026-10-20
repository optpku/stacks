/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.HomologicalDeltaFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Universal Homological Delta Functors

This leaf owns the chosen extension of degree-zero maps.  The choice is hidden behind its
specification and uniqueness lemmas, so clients do not depend on a particular witness.
-/

@[expose] public section

noncomputable section

universe vA uA vB uB

namespace CategoryTheory.HomologicalDeltaFunctor.IsUniversal

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]

/-- The chosen extension of a degree-zero natural transformation into a universal homological
delta functor. -/
@[stacks 010S "universal homological extension of a degree-zero transformation"]
noncomputable def lift {F G : HomologicalDeltaFunctor A B} [IsUniversal F]
    (t : (G 0).obj ⟶ (F 0).obj) : G ⟶ F :=
  Classical.choose (IsUniversal.existsUnique_hom G t)

/-- The degree-zero component of the chosen extension is the prescribed map. -/
@[simp]
theorem lift_app_zero {F G : HomologicalDeltaFunctor A B} [IsUniversal F]
    (t : (G 0).obj ⟶ (F 0).obj) :
    (lift t).app 0 = t :=
  (Classical.choose_spec (IsUniversal.existsUnique_hom G t)).1

/-- Any extension with the prescribed degree-zero component is the chosen extension. -/
theorem lift_unique {F G : HomologicalDeltaFunctor A B} [IsUniversal F]
    (t : (G 0).obj ⟶ (F 0).obj) (τ : G ⟶ F) (hτ : τ.app 0 = t) :
    τ = lift t :=
  (Classical.choose_spec (IsUniversal.existsUnique_hom G t)).2 τ hτ

/-- Extending the degree-zero component of an existing morphism recovers that morphism. -/
@[simp]
theorem lift_of_app {F G : HomologicalDeltaFunctor A B} [IsUniversal F]
    (τ : G ⟶ F) :
    lift (τ.app 0) = τ :=
  (lift_unique (τ.app 0) τ rfl).symm

/-- The extension of the identity degree-zero map is the identity morphism. -/
@[simp]
theorem lift_id (F : HomologicalDeltaFunctor A B) [IsUniversal F] :
    lift (𝟙 ((F 0).obj)) = 𝟙 F := sorry

/-- Universal extension commutes with precomposition by a delta-functor morphism. -/
@[simp]
theorem lift_comp {F G H : HomologicalDeltaFunctor A B} [IsUniversal F]
    (t : (G 0).obj ⟶ (F 0).obj) (τ : H ⟶ G) :
    lift (τ.app 0 ≫ t) = τ ≫ lift t := sorry

end CategoryTheory.HomologicalDeltaFunctor.IsUniversal
