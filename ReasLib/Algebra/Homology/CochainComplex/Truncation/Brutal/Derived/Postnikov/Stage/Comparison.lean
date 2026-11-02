/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Derived.Postnikov

/-!
# Comparison of Brutal-Truncation Stage Triangles

This leaf identifies the shifted triangle coming directly from the short exact truncation row
with the normalized stage triangle stored in the associated Postnikov tower.
-/

@[expose] public section

open CategoryTheory.Pretriangulated
open DerivedCategory

noncomputable section

universe w v u

namespace CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.Stage

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

set_option backward.isDefEq.respectTransparency false in
/-- The first square comparing the short-exact-sequence triangle with the normalized tower
triangle commutes. -/
theorem towerTriangleIso_comm₁ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (triangle K n).mor₁ ≫ (xIso K (n + 1)).hom =
      (leftIso K n).hom ≫ ((tower K).triangle n).mor₁ := by
  have hleft : (leftIso K n).hom =
      (Brutal.Tower.index (n + 1)).negOnePow • 𝟙 (y K (n + 1)) := by
    change (𝟙 _ ≫ ((-1) ^ (Brutal.Tower.index (n + 1)) :
      (CatCenter (DerivedCategory A))ˣ).val.app _) = _
    rw [Category.id_comp]
    exact CatCenter.app_neg_one_zpow _ _
  change
    ((Brutal.Tower.index (n + 1)).negOnePow •
        (Q.map (Trunc.Piece.π K (n + 1)))⟦Brutal.Tower.index (n + 1)⟧') ≫
      (xIso K (n + 1)).hom = (leftIso K n).hom ≫ toX K (n + 1)
  simp only [Q_obj_single_obj, Int.negOnePow_neg, Nat.cast_add, Nat.cast_one,
    Linear.units_smul_comp, hleft, toX, smul_left_cancel_iff]
  exact (Category.id_comp _).symm

/-- The second square comparing the short-exact-sequence triangle with the normalized tower
triangle commutes. -/
theorem towerTriangleIso_comm₂ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (triangle K n).mor₂ ≫ (rightIso K n).hom =
      (xIso K (n + 1)).hom ≫ ((tower K).triangle n).mor₂ := by
  change (triangle K n).mor₂ ≫ (rightIso K n).hom =
    (xIso K (n + 1)).hom ≫ toNext K n
  exact ((xIso K (n + 1)).hom_inv_id_assoc
    ((triangle K n).mor₂ ≫ (rightIso K n).hom)).symm

/-- The connecting square comparing the short-exact-sequence triangle with the normalized tower
triangle commutes. -/
theorem towerTriangleIso_comm₃ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (triangle K n).mor₃ ≫ ((leftIso K n).hom)⟦(1 : ℤ)⟧' =
      (rightIso K n).hom ≫ ((tower K).triangle n).mor₃ := by
  change (triangle K n).mor₃ ≫ ((leftIso K n).hom)⟦(1 : ℤ)⟧' =
    (rightIso K n).hom ≫ connecting K n
  simp only [connecting, Iso.hom_inv_id_assoc]

/-- The triangle obtained directly from two consecutive brutal truncations is canonically
isomorphic to the corresponding normalized triangle of the Postnikov tower. -/
@[stacks 0D8Z "comparison with the normalized brutal Postnikov stage triangle"]
noncomputable def towerTriangleIso (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    triangle K n ≅ (tower K).triangle n :=
  Triangle.isoMk _ _ (leftIso K n) (xIso K (n + 1)) (rightIso K n)
    (towerTriangleIso_comm₁ K n) (towerTriangleIso_comm₂ K n)
      (towerTriangleIso_comm₃ K n)

/-- The first component of the forward stage comparison is the canonical left-vertex iso. -/
@[simp, stacks 0D8Z]
theorem towerTriangleIso.hom₁ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (towerTriangleIso K n).hom.hom₁ = (leftIso K n).hom := rfl

/-- The second component of the forward stage comparison is the cutoff-piece iso. -/
@[simp, stacks 0D8Z]
theorem towerTriangleIso.hom₂ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (towerTriangleIso K n).hom.hom₂ = (xIso K (n + 1)).hom := rfl

/-- The third component of the forward stage comparison is the canonical right-vertex iso. -/
@[simp, stacks 0D8Z]
theorem towerTriangleIso.hom₃ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (towerTriangleIso K n).hom.hom₃ = (rightIso K n).hom := rfl

/-- The first component of the inverse stage comparison is the inverse left-vertex iso. -/
@[simp, stacks 0D8Z]
theorem towerTriangleIso.inv₁ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (towerTriangleIso K n).inv.hom₁ = (leftIso K n).inv := rfl

/-- The second component of the inverse stage comparison is the inverse cutoff-piece iso. -/
@[simp, stacks 0D8Z]
theorem towerTriangleIso.inv₂ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (towerTriangleIso K n).inv.hom₂ = (xIso K (n + 1)).inv := rfl

/-- The third component of the inverse stage comparison is the inverse right-vertex iso. -/
@[simp, stacks 0D8Z]
theorem towerTriangleIso.inv₃ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (towerTriangleIso K n).inv.hom₃ = (rightIso K n).inv := rfl

end CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.Stage
