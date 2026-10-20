/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Closed
public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Shifts compatible with differential graded enrichment

An ordinary shift on the category of closed degree-zero morphisms does not by itself remember
how homogeneous morphisms transform.  `ShiftCompatibility` records that missing enriched data:
degree `k + n` morphisms into `Y` are identified with degree `k` morphisms into `Y⟦n⟧`, and the
identification respects the differential and composition.  This is the degreewise form of the
Hom-complex shift axiom used in the construction of connecting morphisms.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace DifferentialGradedCategory

open scoped DifferentialGradedCategory

/-- Compatibility between integer shifts on `Comp R A` and the differential graded enrichment.

The equivalence `homEquiv X Y n k` is the degree-`k` component of the expected identification
`Hom(X, Y⟦n⟧) ≅ Hom(X, Y)⟦n⟧`.  The remaining fields expose its differential and composition
laws so downstream constructions do not have to unfold a particular model of shifts. -/
@[stacks 09P5 "shifts compatible with differential graded enrichment"]
class ShiftCompatibility
    (R : Type u) [CommRing R]
    (A : Type v) [D : DifferentialGradedCategory.{u, v, w} R A]
    [HasShift (Comp R A) ℤ] : Type (max u v w) where
  /-- The homogeneous equivalence induced by shifting the target. -/
  homEquiv (X Y : Comp R A) (n k : ℤ) :
    (X.obj ⟶[k + n] Y.obj) ≃ₗ[R] (X.obj ⟶[k] (Y⟦n⟧).obj)
  /-- The homogeneous equivalence intertwines the differentials. -/
  map_d (X Y : Comp R A) (n k : ℤ) (f : X.obj ⟶[k + n] Y.obj) :
    homEquiv X Y n (k + 1)
        (castHom (add_right_comm k n 1) (D.d (k + n) f)) =
      D.d k (homEquiv X Y n k f)
  /-- Shifting the target commutes with homogeneous precomposition. -/
  map_precomp {W X Y : Comp R A} (n i j : ℤ)
      (f : W.obj ⟶[i] X.obj) (g : X.obj ⟶[j + n] Y.obj) :
    homEquiv W Y n (i + j)
        (castHom (add_assoc i j n).symm (D.comp g f)) =
      D.comp (homEquiv X Y n j g) f
  /-- Shifting the target commutes with postcomposition by a closed morphism. -/
  map_postcomp {X Y Z : Comp R A} (n k : ℤ)
      (f : X.obj ⟶[k + n] Y.obj) (g : Y ⟶ Z) :
    homEquiv X Z n k
        (castHom (add_zero (k + n)) (D.comp g.val f)) =
      castHom (add_zero k)
        (D.comp (g⟦n⟧').val (homEquiv X Y n k f))

namespace ShiftCompatibility

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ] [ShiftCompatibility R A]

/-- A homogeneous morphism of degree `n`, reinterpreted as a degree-zero morphism into the
target shifted by `n`. -/
def toShiftLinear (X Y : Comp R A) (n : ℤ) :
    (X.obj ⟶[n] Y.obj) →ₗ[R] (X.obj ⟶[0] (Y⟦n⟧).obj) where
  toFun f := homEquiv X Y n 0 (castHom (zero_add n).symm f)
  map_add' := sorry
  map_smul' := sorry

/-- `toShiftLinear` is the degree-zero component of `homEquiv`. -/
@[simp]
theorem toShiftLinear_apply (X Y : Comp R A) (n : ℤ) (f : X.obj ⟶[n] Y.obj) :
    toShiftLinear X Y n f =
      homEquiv X Y n 0 (castHom (zero_add n).symm f) := sorry

/-- A closed homogeneous morphism remains closed when regarded as a degree-zero morphism into
the shifted target. -/
theorem toShiftLinear_closed (X Y : Comp R A) (n : ℤ)
    (f : X.obj ⟶[n] Y.obj) (hf : D.d n f = 0) :
    D.d 0 (toShiftLinear X Y n f) = 0 := sorry

/-- A closed degree-`n` homogeneous morphism as a morphism `X ⟶ Y⟦n⟧` in `Comp R A`. -/
def cycleToShift (X Y : Comp R A) (n : ℤ)
    (f : X.obj ⟶[n] Y.obj) (hf : D.d n f = 0) : X ⟶ Y⟦n⟧ :=
  ⟨toShiftLinear X Y n f, toShiftLinear_closed X Y n f hf⟩

/-- The homogeneous representative of `cycleToShift` is `toShiftLinear`. -/
@[simp]
theorem cycleToShift_val (X Y : Comp R A) (n : ℤ)
    (f : X.obj ⟶[n] Y.obj) (hf : D.d n f = 0) :
    (cycleToShift X Y n f hf).val = toShiftLinear X Y n f := sorry

end ShiftCompatibility

end DifferentialGradedCategory
