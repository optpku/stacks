/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/-- The first square comparing the short-exact-sequence triangle with the normalized tower
triangle commutes. -/
theorem towerTriangleIso_comm₁ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (triangle K n).mor₁ ≫ (xIso K (n + 1)).hom =
      (leftIso K n).hom ≫ ((tower K).triangle n).mor₁ := sorry

/-- The second square comparing the short-exact-sequence triangle with the normalized tower
triangle commutes. -/
theorem towerTriangleIso_comm₂ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (triangle K n).mor₂ ≫ (rightIso K n).hom =
      (xIso K (n + 1)).hom ≫ ((tower K).triangle n).mor₂ := sorry

/-- The connecting square comparing the short-exact-sequence triangle with the normalized tower
triangle commutes. -/
theorem towerTriangleIso_comm₃ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (triangle K n).mor₃ ≫ ((leftIso K n).hom)⟦(1 : ℤ)⟧' =
      (rightIso K n).hom ≫ ((tower K).triangle n).mor₃ := sorry

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
    (towerTriangleIso K n).hom.hom₁ = (leftIso K n).hom := sorry

/-- The second component of the forward stage comparison is the cutoff-piece iso. -/
@[simp, stacks 0D8Z]
theorem towerTriangleIso.hom₂ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (towerTriangleIso K n).hom.hom₂ = (xIso K (n + 1)).hom := sorry

/-- The third component of the forward stage comparison is the canonical right-vertex iso. -/
@[simp, stacks 0D8Z]
theorem towerTriangleIso.hom₃ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (towerTriangleIso K n).hom.hom₃ = (rightIso K n).hom := sorry

/-- The first component of the inverse stage comparison is the inverse left-vertex iso. -/
@[simp, stacks 0D8Z]
theorem towerTriangleIso.inv₁ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (towerTriangleIso K n).inv.hom₁ = (leftIso K n).inv := sorry

/-- The second component of the inverse stage comparison is the inverse cutoff-piece iso. -/
@[simp, stacks 0D8Z]
theorem towerTriangleIso.inv₂ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (towerTriangleIso K n).inv.hom₂ = (xIso K (n + 1)).inv := sorry

/-- The third component of the inverse stage comparison is the inverse right-vertex iso. -/
@[simp, stacks 0D8Z]
theorem towerTriangleIso.inv₃ (K : CochainComplex A ℤ) [K.IsStrictlyLE 0] (n : ℕ) :
    (towerTriangleIso K n).inv.hom₃ = (rightIso K n).inv := sorry

end CategoryTheory.CochainComplex.Brutal.Derived.Postnikov.Stage
