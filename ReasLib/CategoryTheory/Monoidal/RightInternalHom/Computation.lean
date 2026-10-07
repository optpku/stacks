module

public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Adjunction

/-!
# Computation rules for right internal Homs

This leaf records the identity transposes and triangle identities for a chosen right internal-Hom
structure. They are the right-oriented counterparts of the standard `MonoidalClosed` computation
API.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory Opposite
open scoped CategoryTheory.RightInternalHom

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightInternalHom

variable (H : RightInternalHom C)

/-- Uncurrying the identity of a right internal-Hom object gives evaluation. -/
theorem uncurry_id_eq_ev (X Y : C) :
    H.uncurry (𝟙 (X ⟶[H]ᵣ Y)) = H.ev X Y := by
  rw [H.uncurry_eq]
  simp

/-- Currying the identity of `Y ⊗ X` gives coevaluation. -/
theorem curry_id_eq_coev (X Y : C) :
    H.curry (𝟙 (Y ⊗ X)) = H.coev X Y := by
  rw [H.curry_eq]
  simp

/-- Coevaluation followed by evaluation is the identity on `Y ⊗ X`. -/
@[reassoc (attr := simp)]
theorem ev_coev (X Y : C) :
    (H.coev X Y ▷ X) ≫ H.ev X (Y ⊗ X) = 𝟙 (Y ⊗ X) := by
  exact (H.adj₂.adj X).left_triangle_components Y

/-- Coevaluation followed by the right internal-Hom image of evaluation is the identity. -/
@[reassoc (attr := simp)]
theorem coev_ev (X Y : C) :
    H.coev X (X ⟶[H]ᵣ Y) ≫
      (H.hom.obj (op X)).map (H.ev X Y) = 𝟙 (X ⟶[H]ᵣ Y) := by
  exact (H.adj₂.adj X).right_triangle_components Y

end RightInternalHom

end CategoryTheory
