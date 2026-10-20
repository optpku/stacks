/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Restricting scheme-theoretic images

For a quasi-compact morphism, the kernel ideal sheaf and the scheme-theoretic image commute
with restriction to an open subscheme of the target.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

noncomputable section

variable {X Y : Scheme.{u}}

private lemma eqToIso_subscheme_hom_subschemeι
    {I J : X.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫ J.subschemeι =
      I.subschemeι := by
  subst J
  simp

namespace Scheme.Hom

/-- The kernel ideal sheaf of a quasi-compact morphism commutes with restriction to an open
subscheme of the target. -/
theorem ker_morphismRestrict (f : X ⟶ Y) [QuasiCompact f] (U : Y.Opens) :
    (f ∣_ U).ker = f.ker.comap U.ι := by
  ext V x
  rw [Scheme.ker_morphismRestrict_ideal,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv, Ideal.mem_comap,
    Scheme.Hom.ker_apply, RingHom.mem_ker]
  rfl

/-- The scheme-theoretic image of a quasi-compact morphism restricted to an open is
canonically isomorphic to the restriction of its scheme-theoretic image. -/
noncomputable def imageMorphismRestrictIso (f : X ⟶ Y) [QuasiCompact f] (U : Y.Opens) :
    (f ∣_ U).image ≅ (f.imageι ⁻¹ᵁ U) :=
  let h := ker_morphismRestrict f U
  eqToIso (congrArg Scheme.IdealSheafData.subscheme h) ≪≫
    f.ker.comapIso U.ι ≪≫
    pullbackSymmetry U.ι f.imageι ≪≫
    pullbackRestrictIsoRestrict f.imageι U

/-- The image-restriction isomorphism commutes with the closed immersions into the restricted
target. -/
@[reassoc]
theorem imageMorphismRestrictIso_hom_imageι
    (f : X ⟶ Y) [QuasiCompact f] (U : Y.Opens) :
    (imageMorphismRestrictIso f U).hom ≫ (f.imageι ∣_ U) = (f ∣_ U).imageι := by
  let h := ker_morphismRestrict f U
  change
    ((eqToIso (congrArg Scheme.IdealSheafData.subscheme h) ≪≫
      f.ker.comapIso U.ι ≪≫
      pullbackSymmetry U.ι f.imageι ≪≫
      pullbackRestrictIsoRestrict f.imageι U).hom ≫
        (f.imageι ∣_ U)) =
      (f ∣_ U).ker.subschemeι
  rw [← cancel_mono U.ι]
  simp only [Iso.trans_hom, Category.assoc, morphismRestrict_ι,
    pullbackRestrictIsoRestrict_hom_ι_assoc,
    pullbackSymmetry_hom_comp_fst_assoc]
  simp only [← pullback.condition]
  simp only [Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  rw [← Category.assoc, eqToIso_subscheme_hom_subschemeι]
  exact h

end Scheme.Hom

end


end AlgebraicGeometry
