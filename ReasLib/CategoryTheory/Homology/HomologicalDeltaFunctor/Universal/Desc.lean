/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/-- The chosen extension of a degree-zero natural transformation out of a universal homological
delta functor. -/
@[stacks 010S "universal homological extension of a degree-zero transformation"]
noncomputable def desc {F G : HomologicalDeltaFunctor A B} [IsUniversal F]
    (t : (F 0).obj ⟶ (G 0).obj) : F ⟶ G :=
  Classical.choose (IsUniversal.existsUnique_hom G t)

/-- The degree-zero component of the chosen extension is the prescribed map. -/
@[simp]
theorem desc_app_zero {F G : HomologicalDeltaFunctor A B} [IsUniversal F]
    (t : (F 0).obj ⟶ (G 0).obj) :
    (desc t).app 0 = t := sorry

/-- Any extension with the prescribed degree-zero component is the chosen extension. -/
theorem desc_unique {F G : HomologicalDeltaFunctor A B} [IsUniversal F]
    (t : (F 0).obj ⟶ (G 0).obj) (τ : F ⟶ G) (hτ : τ.app 0 = t) :
    τ = desc t := sorry

/-- Extending the degree-zero component of an existing morphism recovers that morphism. -/
@[simp]
theorem desc_of_app {F G : HomologicalDeltaFunctor A B} [IsUniversal F]
    (τ : F ⟶ G) :
    desc (τ.app 0) = τ := sorry

/-- The extension of the identity degree-zero map is the identity morphism. -/
@[simp]
theorem desc_id (F : HomologicalDeltaFunctor A B) [IsUniversal F] :
    desc (𝟙 ((F 0).obj)) = 𝟙 F := sorry

/-- Universal extension commutes with postcomposition by a delta-functor morphism. -/
@[simp]
theorem desc_comp {F G H : HomologicalDeltaFunctor A B} [IsUniversal F]
    (t : (F 0).obj ⟶ (G 0).obj) (σ : G ⟶ H) :
    desc (t ≫ σ.app 0) = desc t ≫ σ := sorry

end CategoryTheory.HomologicalDeltaFunctor.IsUniversal
