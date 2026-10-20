/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Adjunction

/-!
# Change-of-choice API for right internal Homs

Two chosen right internal-Hom structures are canonically isomorphic. This leaf records how that
isomorphism transports their currying and enriched-style structure maps, without exposing the
underlying parametrized-adjunction uniqueness construction.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open MonoidalCategory Opposite
open scoped CategoryTheory.RightInternalHom

noncomputable section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

set_option backward.isDefEq.respectTransparency false

namespace RightInternalHom

/-- The inverse component of the canonical change-of-choice isomorphism is the forward component
of the canonical change from `H'` back to `H`. -/
theorem uniqueIso.inv.app (H H' : RightInternalHom C) (X Y : C) :
    ((H.uniqueIso H').app (op X)).inv.app Y =
      ((H'.uniqueIso H).app (op X)).hom.app Y := by
  simpa only [uniqueIso.app] using
    Adjunction.rightAdjointUniq_inv_app (H.adj₂.adj X) (H'.adj₂.adj X) Y

/-- Canonical changes of right internal-Hom choice compose transitively. -/
@[reassoc]
theorem uniqueIso.hom.trans (H H' H'' : RightInternalHom C) :
    (H.uniqueIso H').hom ≫ (H'.uniqueIso H'').hom = (H.uniqueIso H'').hom := by
  ext X Y
  simp only [NatTrans.comp_app]
  exact Adjunction.rightAdjointUniq_trans_app _ _ _ _

/-- The component form of transitivity for canonical changes of right internal-Hom choice. -/
@[reassoc]
theorem uniqueIso.hom.trans.app (H H' H'' : RightInternalHom C) (X Y : C) :
    ((H.uniqueIso H').app (op X)).hom.app Y ≫
        ((H'.uniqueIso H'').app (op X)).hom.app Y =
      ((H.uniqueIso H'').app (op X)).hom.app Y := by
  simp only [uniqueIso.app]
  exact Adjunction.rightAdjointUniq_trans_app _ _ _ _

/-- The canonical change from a chosen right internal Hom to itself is the identity. -/
@[simp]
theorem uniqueIso.hom.refl (H : RightInternalHom C) :
    (H.uniqueIso H).hom = 𝟙 H.hom := by
  ext X Y
  simp only [NatTrans.id_app]
  exact NatTrans.congr_app (Adjunction.rightAdjointUniq_refl (H.adj₂.adj (unop X))) Y

/-- The component form of the identity canonical change of right internal-Hom choice. -/
@[simp]
theorem uniqueIso.hom.refl.app (H : RightInternalHom C) (X Y : C) :
    ((H.uniqueIso H).app (op X)).hom.app Y = 𝟙 _ := by
  simp only [uniqueIso.app]
  exact NatTrans.congr_app (Adjunction.rightAdjointUniq_refl (H.adj₂.adj X)) Y

/-- Currying through `H` and then applying the canonical change-of-choice map agrees with
currying through `H'`. -/
@[reassoc]
theorem uniqueIso.hom.app.curry (H H' : RightInternalHom C) {X W Y : C}
    (f : W ⊗ X ⟶ Y) :
    H.curry f ≫ ((H.uniqueIso H').app (op X)).hom.app Y = H'.curry f := by
  change ((tensoringRight C).obj X).obj W ⟶ Y at f
  simp only [RightInternalHom.curry, RightInternalHom.homEquiv]
  change (H.adj₂.adj X).homEquiv W Y f ≫
      ((H.uniqueIso H').app (op X)).hom.app Y =
    (H'.adj₂.adj X).homEquiv W Y f
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rw [Category.assoc, ((H.uniqueIso H').app (op X)).hom.naturality f]
  rw [← Category.assoc, uniqueIso.app]
  rw [Adjunction.unit_rightAdjointUniq_hom_app]

/-- Uncurrying after the canonical change-of-choice map agrees with uncurrying through the
original right internal-Hom structure. -/
@[reassoc]
theorem uniqueIso.hom.app.uncurry (H H' : RightInternalHom C) {X W Y : C}
    (f : W ⟶ (X ⟶[H]ᵣ Y)) :
    H'.uncurry (f ≫ ((H.uniqueIso H').app (op X)).hom.app Y) = H.uncurry f := by
  simp only [RightInternalHom.uncurry, RightInternalHom.homEquiv, uniqueIso.app]
  change ((H'.adj₂.adj X).homEquiv W Y).symm
      (f ≫ ((H.adj₂.adj X).rightAdjointUniq (H'.adj₂.adj X)).hom.app Y) =
    ((H.adj₂.adj X).homEquiv W Y).symm f
  rw [Adjunction.homEquiv_naturality_left_symm]
  rw [Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
  exact ((H.adj₂.adj X).homEquiv_counit W Y f).symm

/-- The canonical change-of-choice map intertwines evaluations. -/
@[reassoc]
theorem uniqueIso.hom.app.ev (H H' : RightInternalHom C) (X Y : C) :
    (((H.uniqueIso H').app (op X)).hom.app Y ▷ X) ≫ H'.ev X Y = H.ev X Y := by
  simp only [RightInternalHom.ev, uniqueIso.app]
  change ((tensoringRight C).obj X).map
      (((H.adj₂.adj X).rightAdjointUniq (H'.adj₂.adj X)).hom.app Y) ≫
        (H'.adj₂.adj X).counit.app Y = (H.adj₂.adj X).counit.app Y
  exact Adjunction.rightAdjointUniq_hom_app_counit
    (H.adj₂.adj X) (H'.adj₂.adj X) Y

/-- The inverse canonical change-of-choice map intertwines evaluations. -/
@[reassoc]
theorem uniqueIso.inv.app.ev (H H' : RightInternalHom C) (X Y : C) :
    (((H.uniqueIso H').app (op X)).inv.app Y ▷ X) ≫ H.ev X Y = H'.ev X Y := by
  rw [uniqueIso.inv.app]
  exact uniqueIso.hom.app.ev H' H X Y

/-- Coevaluation through `H` followed by the canonical change-of-choice map is coevaluation
through `H'`. -/
@[reassoc]
theorem uniqueIso.hom.app.coev (H H' : RightInternalHom C) (X Y : C) :
    H.coev X Y ≫ ((H.uniqueIso H').app (op X)).hom.app (Y ⊗ X) = H'.coev X Y := by
  simp only [RightInternalHom.coev, uniqueIso.app]
  change (H.adj₂.adj X).unit.app Y ≫
      ((H.adj₂.adj X).rightAdjointUniq
        (H'.adj₂.adj X)).hom.app (((tensoringRight C).obj X).obj Y) =
    (H'.adj₂.adj X).unit.app Y
  exact Adjunction.unit_rightAdjointUniq_hom_app
    (H.adj₂.adj X) (H'.adj₂.adj X) Y

/-- Coevaluation through `H'` followed by the inverse canonical change-of-choice map is
coevaluation through `H`. -/
@[reassoc]
theorem uniqueIso.inv.app.coev (H H' : RightInternalHom C) (X Y : C) :
    H'.coev X Y ≫ ((H.uniqueIso H').app (op X)).inv.app (Y ⊗ X) = H.coev X Y := by
  rw [uniqueIso.inv.app]
  exact uniqueIso.hom.app.coev H' H X Y

/-- The canonical change-of-choice map preserves internal-Hom identities. -/
@[reassoc]
theorem uniqueIso.hom.app.id (H H' : RightInternalHom C) (X : C) :
    H.id X ≫ ((H.uniqueIso H').app (op X)).hom.app X = H'.id X := by
  simpa only [RightInternalHom.id] using
    uniqueIso.hom.app.curry H H' (λ_ X).hom

/-- The canonical change-of-choice map preserves internal-Hom composition. -/
@[reassoc]
theorem uniqueIso.hom.app.comp (H H' : RightInternalHom C) (X Y Z : C) :
    ((((H.uniqueIso H').app (op Y)).hom.app Z) ⊗ₘ
        (((H.uniqueIso H').app (op X)).hom.app Y)) ≫ H'.comp X Y Z =
      H.comp X Y Z ≫ ((H.uniqueIso H').app (op X)).hom.app Z := by
  apply H'.uncurry_injective
  rw [H'.uncurry_natural_left]
  rw [uniqueIso.hom.app.uncurry H H' (H.comp X Y Z)]
  simp only [RightInternalHom.comp]
  change _ ≫ H'.uncurry (H'.curry _) = H.uncurry (H.curry _)
  rw [H'.uncurry_curry, H.uncurry_curry]
  rw [← uniqueIso.hom.app.ev H H' X Y, ← uniqueIso.hom.app.ev H H' Y Z]
  simp [tensorHom_def, Category.assoc]
  rw [MonoidalCategory.associator_naturality_left_assoc]
  rw [← MonoidalCategory.whisker_exchange_assoc]
  rw [← MonoidalCategory.whisker_exchange_assoc]

/-- The canonical change-of-choice map preserves the left-tensor internal-Hom morphism. -/
@[reassoc]
theorem uniqueIso.hom.app.tensorLeft (H H' : RightInternalHom C) (X Y Z : C) :
    (Z ◁ ((H.uniqueIso H').app (op X)).hom.app Y) ≫ H'.tensorLeft X Y Z =
      H.tensorLeft X Y Z ≫ ((H.uniqueIso H').app (op X)).hom.app (Z ⊗ Y) := by
  apply H'.uncurry_injective
  rw [H'.uncurry_natural_left]
  rw [uniqueIso.hom.app.uncurry H H' (H.tensorLeft X Y Z)]
  simp only [RightInternalHom.tensorLeft]
  change _ ≫ H'.uncurry (H'.curry _) = H.uncurry (H.curry _)
  rw [H'.uncurry_curry, H.uncurry_curry]
  rw [← uniqueIso.hom.app.ev H H' X Y]
  monoidal

end RightInternalHom

end

end CategoryTheory
