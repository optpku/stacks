/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Smooth
public import ReasLib.AlgebraicGeometry.ChowGroup.Dedekind.ExteriorProduct.Cap
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Cycle
public import ReasLib.AlgebraicGeometry.ChowGroup.Total
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.SchemeOverField AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

variable {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Smooth X.hom] [Smooth Y.hom]

/-- The canonical Gysin class between smooth schemes of dimensions `d` and `e` is the
inverse image of the source smooth orientation under composition with the target orientation. -/
def smoothGysinClassOfDimensions (f : X ⟶ Y) (d e : ℕ)
    [RelativeDimension X.hom d] [RelativeDimension Y.hom e] :
    group (fun _ ↦ 0) f ((e : ℤ) - d) :=
  (compSmoothEquiv (fun _ ↦ 0) f (terminal.from Y) e ((e : ℤ) - d)).symm
    (Eq.mpr (congrArg (fun g : X ⟶ ⊤_ (SchemeOverField k) ↦
    BivariantClass (fun _ ↦ 0) g ((e : ℤ) - d - e))
    (Subsingleton.elim (f ≫ terminal.from Y) (terminal.from X)))
    (Eq.mpr (congrArg (fun p : ℤ ↦
      BivariantClass (fun _ ↦ 0) (terminal.from X) p)
      (show (e : ℤ) - d - e = -(d : ℤ) by omega))
      (flatPullback (fun _ ↦ 0) (terminal.from X) d)))

/-- Composing the canonical Gysin class with the target smooth orientation yields the
source smooth orientation. -/
theorem smoothGysinClassOfDimensions_comp (f : X ⟶ Y) (d e : ℕ)
    [RelativeDimension X.hom d] [RelativeDimension Y.hom e] :
    compSmoothEquiv (fun _ ↦ 0) f (terminal.from Y) e ((e : ℤ) - d)
      (smoothGysinClassOfDimensions f d e) =
    (Eq.mpr (congrArg (fun g : X ⟶ ⊤_ (SchemeOverField k) ↦
    BivariantClass (fun _ ↦ 0) g ((e : ℤ) - d - e))
    (Subsingleton.elim (f ≫ terminal.from Y) (terminal.from X)))
    (Eq.mpr (congrArg (fun p : ℤ ↦
      BivariantClass (fun _ ↦ 0) (terminal.from X) p)
      (show (e : ℤ) - d - e = -(d : ℤ) by omega))
      (flatPullback (fun _ ↦ 0) (terminal.from X) d))) := sorry

end AlgebraicGeometry.BivariantClass

namespace AlgebraicGeometry.ChowGroup

variable {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Smooth X.hom] [Smooth Y.hom]

/-- The integral Gysin action between smooth constant-dimensional schemes, assembled
from identity-square cap maps on homogeneous Chow classes. -/
def smoothGysinMapOfDimensions (f : X ⟶ Y) (d e : ℕ)
    [RelativeDimension X.hom d] [RelativeDimension Y.hom e] :
    Total (fun _ ↦ 0) Y →+ Total (fun _ ↦ 0) X :=
  Dedekind.Total.cap (fun _ ↦ 0)
    (BivariantClass.smoothGysinClassOfDimensions f d e)
    (𝟙 X) f (𝟙 Y) IsPullback.of_id_fst

/-- On a homogeneous input the smooth Gysin action is cap in degree `n - (e - d)`. -/
theorem smoothGysinMapOfDimensions_of (f : X ⟶ Y) (d e : ℕ)
    [RelativeDimension X.hom d] [RelativeDimension Y.hom e] (n : ℤ)
    (a : RelativeChow (fun _ ↦ 0) Y n) :
    smoothGysinMapOfDimensions f d e (DirectSum.of _ n a) =
      DirectSum.of _ (n - ((e : ℤ) - d))
        ((BivariantClass.smoothGysinClassOfDimensions f d e).cap
          (𝟙 X) f (𝟙 Y) IsPullback.of_id_fst n a) := by
  exact Dedekind.Total.cap_of _ _ _ _ _ _ _ _

/-- Smooth Gysin pullback carries the target fundamental class to the source fundamental class. -/
theorem smoothGysinMapOfDimensions_fundamental (f : X ⟶ Y) (d e : ℕ)
    [RelativeDimension X.hom d] [RelativeDimension Y.hom e] :
    smoothGysinMapOfDimensions f d e
      (DirectSum.of _ (e : ℤ) (RelativeChow.fundamentalClass (fun _ ↦ 0) Y e)) =
      DirectSum.of _ (d : ℤ) (RelativeChow.fundamentalClass (fun _ ↦ 0) X d) := sorry

end AlgebraicGeometry.ChowGroup
