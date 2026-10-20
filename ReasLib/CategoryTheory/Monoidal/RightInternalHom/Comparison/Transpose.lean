module

public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Comparison

/-!
# Change of choice for nested right internal Homs

The canonical comparison between two chosen right internal-Hom structures also compares nested
internal Homs. This file packages that comparison and records its compatibility with the
composition transpose in a braided monoidal category.
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

/-- The canonical change-of-choice isomorphism between nested right internal Homs. It changes
the outer right internal-Hom structure covariantly, then changes the inner parameter
contravariantly. -/
noncomputable def uniqueIso.app.nestedIso (H H' : RightInternalHom C) (X Y Z : C) :
    ((X ⟶[H]ᵣ Y) ⟶[H]ᵣ Z) ≅ ((X ⟶[H']ᵣ Y) ⟶[H']ᵣ Z) :=
  ((H.uniqueIso H').app (op (X ⟶[H]ᵣ Y))).app Z ≪≫
    (H'.hom.mapIso (((H.uniqueIso H').app (op X)).app Y).symm.op).app Z

namespace uniqueIso.app.nestedIso

/-- The forward nested comparison is the outer change of choice followed by the
contravariant action of the inner inverse comparison. -/
theorem hom (H H' : RightInternalHom C) (X Y Z : C) :
    (uniqueIso.app.nestedIso H H' X Y Z).hom =
      ((H.uniqueIso H').app (op (X ⟶[H]ᵣ Y))).hom.app Z ≫
        (H'.hom.map (((H.uniqueIso H').app (op X)).inv.app Y).op).app Z := by
  rfl

/-- The inverse nested comparison first changes the inner parameter covariantly and then applies
the inverse outer change of choice. -/
theorem inv (H H' : RightInternalHom C) (X Y Z : C) :
    (uniqueIso.app.nestedIso H H' X Y Z).inv =
      (H'.hom.map (((H.uniqueIso H').app (op X)).hom.app Y).op).app Z ≫
        ((H.uniqueIso H').app (op (X ⟶[H]ᵣ Y))).inv.app Z := by
  rfl

end uniqueIso.app.nestedIso

section Braided

variable [BraidedCategory C]

/-- The forward canonical change of right internal-Hom choice intertwines the
composition transpose with the nested comparison. -/
@[reassoc]
theorem uniqueIso.hom.app.compTranspose
    (H H' : RightInternalHom C) (X Y Z : C) :
    (((H.uniqueIso H').app (op Y)).hom.app Z ▷ X) ≫
        H'.compTranspose X Y Z =
      H.compTranspose X Y Z ≫
        (uniqueIso.app.nestedIso H H' X Y Z).hom := by
  apply H'.uncurry_injective
  rw [H'.uncurry_natural_left]
  rw [uniqueIso.app.nestedIso.hom]
  conv_rhs => rw [← Category.assoc]
  rw [H'.uncurry_natural_parameter]
  rw [uniqueIso.hom.app.uncurry H H' (H.compTranspose X Y Z)]
  simp only [RightInternalHom.compTranspose]
  change _ ≫ H'.uncurry (H'.curry _) = _ ≫ H.uncurry (H.curry _)
  rw [H'.uncurry_curry, H.uncurry_curry]
  rw [← uniqueIso.hom.app.ev H H' X Y,
    ← uniqueIso.hom.app.ev H H' Y Z]
  rw [MonoidalCategory.associator_naturality_left_assoc]
  rw [← MonoidalCategory.whisker_exchange_assoc]
  rw [← MonoidalCategory.whisker_exchange_assoc]
  rw [MonoidalCategory.associator_naturality_right_assoc]
  have hinner :
      (X ◁ ((H.uniqueIso H').app (op X)).inv.app Y) ≫
          (β_ X (X ⟶[H]ᵣ Y)).hom ≫
          (((H.uniqueIso H').app (op X)).hom.app Y ▷ X) =
        (β_ X (X ⟶[H']ᵣ Y)).hom := by
    rw [BraidedCategory.braiding_naturality_right_assoc]
    simp
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp only [Category.assoc]
  rw [reassoc_of% hinner]

/-- The inverse canonical change of right internal-Hom choice intertwines the
composition transpose with the inverse nested comparison. -/
@[reassoc]
theorem uniqueIso.inv.app.compTranspose
    (H H' : RightInternalHom C) (X Y Z : C) :
    (((H.uniqueIso H').app (op Y)).inv.app Z ▷ X) ≫
        H.compTranspose X Y Z =
      H'.compTranspose X Y Z ≫
        (uniqueIso.app.nestedIso H H' X Y Z).inv := by
  apply (cancel_epi
    (((H.uniqueIso H').app (op Y)).hom.app Z ▷ X)).1
  rw [← MonoidalCategory.comp_whiskerRight_assoc]
  simp only [Iso.hom_inv_id_app, MonoidalCategory.id_whiskerRight,
    Category.id_comp]
  rw [uniqueIso.hom.app.compTranspose_assoc H H' X Y Z]
  simp

end Braided

end RightInternalHom

end

end CategoryTheory
