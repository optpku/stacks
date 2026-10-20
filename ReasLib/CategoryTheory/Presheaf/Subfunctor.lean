module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import ReasLib.CategoryTheory.Presheaf.Basic

/-!
# Subpresheaves and image factorization

The range subfunctor supplies the canonical epi-mono factorization of a
morphism of type-valued presheaves.
-/

@[expose] public section

universe u v w

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C]

/-- A morphism of presheaves factors through a unique subpresheaf of its target with an
epimorphic first map. -/
theorem existsUnique_epiFactorization {F G : Presheaf C} (φ : F ⟶ G) :
    ∃! H : Subfunctor G,
      ∃ α : F ⟶ H.toFunctor, Epi α ∧ α ≫ H.ι = φ := sorry

/-- A subpresheaf admits an epimorphic factorization of a morphism through its inclusion
if and only if it is the range subfunctor of that morphism. -/
theorem epiFactorization_iff_range {F G : Presheaf C} (φ : F ⟶ G) (H : Subfunctor G) :
    (∃ α : F ⟶ H.toFunctor, Epi α ∧ α ≫ H.ι = φ) ↔ H = range φ := sorry

end CategoryTheory.Subfunctor
