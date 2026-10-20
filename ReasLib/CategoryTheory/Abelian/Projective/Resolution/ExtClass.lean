module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Abelian.Projective.Ext

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.ProjectiveResolution

open Abelian Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {X : C}

/-- The preceding differential composes trivially with the factorization of the next
differential through its image. -/
theorem d_comp_factorThruImage (P : ProjectiveResolution X) (e : ℕ) :
    P.complex.d (e + 2) (e + 1) ≫
      Limits.factorThruImage (P.complex.d (e + 1) e) = 0 :=
  Limits.comp_factorThruImage_eq_zero (P.complex.d_comp_d _ _ _)

/-- The canonical degree-`e + 1` extension class with coefficient object presented as the
image of the differential into degree `e`. -/
noncomputable def resolutionImageExtClass (P : ProjectiveResolution X) (e : ℕ) :
    Ext X (Limits.image (P.complex.d (e + 1) e)) (e + 1) :=
  P.extMk (Limits.factorThruImage (P.complex.d (e + 1) e))
    (e + 2) rfl (P.d_comp_factorThruImage e)

/-- The resolution image class is represented by the differential factored through its image. -/
theorem resolutionImageExtClass_eq_extMk (P : ProjectiveResolution X) (e : ℕ) :
    P.resolutionImageExtClass e =
      P.extMk (Limits.factorThruImage (P.complex.d (e + 1) e))
        (e + 2) rfl (P.d_comp_factorThruImage e) := sorry

end CategoryTheory.ProjectiveResolution
