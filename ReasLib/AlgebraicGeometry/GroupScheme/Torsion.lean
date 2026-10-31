/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import ReasLib.AlgebraicGeometry.GroupScheme.MulBy
public import ReasLib.AlgebraicGeometry.GroupScheme.Torsion.Bundled

/-!
# Torsion group schemes
-/

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The underlying scheme morphism of the bundled multiplication-by-`n` morphism is the
multiplication-by-`n` morphism of the group scheme. -/
theorem grpMulBy_hom (A : SchemeOverField k) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    (CategoryTheory.GrpObj.mulBy (Grp.mk A) n).hom.hom.left = mulBy A n := by
  simp [mulBy, CategoryTheory.GrpObj.mulBy, CategoryTheory.Grp.Hom.hom_pow,
    CategoryTheory.Mon.Hom.hom_pow]

/--
The old bundled name is a thin view of the arbitrary-base canonical kernel.
Its group structure is owned by `Scheme.GroupObject.multiplicationKernelGrpObj`.
-/
noncomputable def torsionGroupScheme (A : SchemeOverField k) [GrpObj A] [IsCommMonObj A]
    (n : ℕ) : Grp (SchemeOverField k) :=
  AlgebraicGeometry.Scheme.GroupObject.multiplicationKernelGroup A n

/-- The legacy bundled carrier is definitionally the canonical kernel carrier. -/
@[simp]
theorem torsionGroupScheme_X_eq_multiplicationKernel (A : SchemeOverField k)
    [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    (torsionGroupScheme A n).X =
      AlgebraicGeometry.Scheme.GroupObject.multiplicationKernel A n := rfl

/-- Named group-object comparison retained for old field-specific consumers. -/
noncomputable def torsionGroupSchemeIso (A : SchemeOverField k) [GrpObj A]
    [IsCommMonObj A] (n : ℕ) :
    torsionGroupScheme A n ≅
      AlgebraicGeometry.Scheme.GroupObject.multiplicationKernelGroup A n :=
  Iso.refl _

/-- The underlying `Over` comparison with the canonical kernel. -/
noncomputable def torsionGroupScheme_X_iso (A : SchemeOverField k) [GrpObj A]
    [IsCommMonObj A] (n : ℕ) :
    (torsionGroupScheme A n).X ≅
      AlgebraicGeometry.Scheme.GroupObject.multiplicationKernel A n :=
  Iso.refl _

/-- The actual inclusion used by the canonical kernel, through the legacy name. -/
noncomputable abbrev torsionGroupScheme_inclusion (A : SchemeOverField k) [GrpObj A]
    [IsCommMonObj A] (n : ℕ) :
    (torsionGroupScheme A n).X ⟶ A :=
  AlgebraicGeometry.Scheme.GroupObject.kernelInclusion A n

@[simp]
theorem torsionGroupScheme_X_iso_hom_comp_inclusion (A : SchemeOverField k)
    [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    (torsionGroupScheme_X_iso A n).hom ≫ torsionGroupScheme_inclusion A n =
      AlgebraicGeometry.Scheme.GroupObject.kernelInclusion A n := by
  simp [torsionGroupScheme_X_iso]

/-- Legacy equation for the bundled categorical pullback. The canonical torsion
constructor above uses the actual scheme fibre and its represented group structure. -/
theorem torsionGroupScheme_condition (A : SchemeOverField k) [GrpObj A] [IsCommMonObj A]
    (n : ℕ) :
    Limits.pullback.fst (CategoryTheory.GrpObj.mulBy (Grp.mk A) n) (Grp.ofHom η[A]) ≫
        CategoryTheory.GrpObj.mulBy (Grp.mk A) n =
      Limits.pullback.snd (CategoryTheory.GrpObj.mulBy (Grp.mk A) n) (Grp.ofHom η[A]) ≫
        Grp.ofHom η[A] := by
  exact Limits.pullback.condition

end AlgebraicGeometry.SchemeOverField
