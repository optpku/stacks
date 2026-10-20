module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import ReasLib.AlgebraicGeometry.GroupScheme.MulBy

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
    (CategoryTheory.GrpObj.mulBy (Grp.mk A) n).hom.hom.left = mulBy A n := sorry

/-- The `n`-torsion group scheme, constructed as the kernel of multiplication by `n`. -/
noncomputable def torsionGroupScheme (A : SchemeOverField k) [GrpObj A] [IsCommMonObj A]
    (n : ℕ) : Grp (SchemeOverField k) :=
  Limits.pullback (CategoryTheory.GrpObj.mulBy (Grp.mk A) n) (Grp.ofHom η[A])

/-- The defining pullback equation for the `n`-torsion group scheme. -/
theorem torsionGroupScheme_condition (A : SchemeOverField k) [GrpObj A] [IsCommMonObj A]
    (n : ℕ) :
    Limits.pullback.fst (CategoryTheory.GrpObj.mulBy (Grp.mk A) n) (Grp.ofHom η[A]) ≫
        CategoryTheory.GrpObj.mulBy (Grp.mk A) n =
      Limits.pullback.snd (CategoryTheory.GrpObj.mulBy (Grp.mk A) n) (Grp.ofHom η[A]) ≫
        Grp.ofHom η[A] := sorry

end AlgebraicGeometry.SchemeOverField
