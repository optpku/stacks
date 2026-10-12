/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Basic

/-!
# Naturality for right internal Homs

This leaf owns the separate and joint variable naturality laws for evaluation and coevaluation.
-/

@[expose] public section

universe v u

namespace CategoryTheory.RightInternalHom

open MonoidalCategory Opposite
open scoped CategoryTheory.RightInternalHom

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (H : RightInternalHom C)

/-- Evaluation is natural in its target. -/
@[reassoc]
theorem ev_natural_target {X Y Y' : C} (g : Y ⟶ Y') :
    ((H.hom.obj (op X)).map g ▷ X) ≫ H.ev X Y' = H.ev X Y ≫ g := by
  exact (H.adj₂.adj X).counit.naturality g

/-- Evaluation is natural contravariantly in its internal-Hom parameter. -/
@[reassoc]
theorem ev_natural_parameter {X X' Y : C} (f : X' ⟶ X) :
    ((H.hom.map f.op).app Y ▷ X') ≫ H.ev X' Y =
      ((X ⟶[H]ᵣ Y) ◁ f) ≫ H.ev X Y := by
  exact (NatTrans.congr_app (H.adj₂.whiskerLeft_map_counit f) Y).symm

/-- Coevaluation is natural in the variable occurring in its source. -/
@[reassoc]
theorem coev_natural_target {X Y Y' : C} (g : Y ⟶ Y') :
    g ≫ H.coev X Y' =
      H.coev X Y ≫ (H.hom.obj (op X)).map (g ▷ X) := by
  exact (H.adj₂.adj X).unit.naturality g

/-- Coevaluation is natural in the internal-Hom parameter: changing the parameter after
coevaluation agrees with changing the tensor factor in its target. -/
@[reassoc]
theorem coev_natural_parameter {X X' Y : C} (f : X ⟶ X') :
    H.coev X' Y ≫ (H.hom.map f.op).app (Y ⊗ X') =
      H.coev X Y ≫ (H.hom.obj (op X)).map (Y ◁ f) := by
  exact (NatTrans.congr_app (H.adj₂.unit_whiskerRight_map f) Y).symm

/-- Coevaluation is jointly natural in its source and internal-Hom parameter. -/
@[reassoc]
theorem coev_natural {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y') :
    g ≫ H.coev X' Y' ≫ (H.hom.map f.op).app (Y' ⊗ X') =
      H.coev X Y ≫ (H.hom.obj (op X)).map (g ⊗ₘ f) := by
  rw [coev_natural_parameter H f]
  rw [← Category.assoc, coev_natural_target H g]
  simp only [Category.assoc, ← Functor.map_comp, tensorHom_def]

end CategoryTheory.RightInternalHom
