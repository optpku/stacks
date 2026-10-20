/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (sbar : GeometricPoint S)
variable (RshS : Type u) [CommRing RshS]
variable [Algebra (S.presheaf.stalk sbar.image) RshS]
variable [IsStrictHenselizationOf (S.presheaf.stalk sbar.image) RshS]

/-- The comparison `Spec(κ(s̄)) ⟶ Spec(O^{sh}_{S,s̄})` over `S` induces
`X ×_S Spec(κ(s̄)) ⟶ X ×_S Spec(O^{sh}_{S,s̄})`. -/
def geometricFiberToHenselized
    (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar RshS)
    (hiS : iS ≫ strictHenselizationMap S sbar RshS = sbar.hom) :
    pullback f sbar.hom ⟶ pullback f (strictHenselizationMap S sbar RshS) :=
  pullback.map f sbar.hom f (strictHenselizationMap S sbar RshS) (𝟙 X) iS (𝟙 S)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id sbar.hom).trans hiS.symm)

/-- The geometric-fibre comparison is a morphism of `X`-schemes. -/
theorem geometricFiberToHenselized_comp_toX
    (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar RshS)
    (hiS : iS ≫ strictHenselizationMap S sbar RshS = sbar.hom) :
    geometricFiberToHenselized f sbar RshS iS hiS ≫
        pullback.fst f (strictHenselizationMap S sbar RshS) =
      pullback.fst f sbar.hom := sorry

/-- The geometric-fibre comparison lies over `Spec(κ(s̄)) ⟶ Spec(O^{sh}_{S,s̄})`. -/
theorem geometricFiberToHenselized_comp_toBase
    (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar RshS)
    (hiS : iS ≫ strictHenselizationMap S sbar RshS = sbar.hom) :
    geometricFiberToHenselized f sbar RshS iS hiS ≫
        pullback.snd f (strictHenselizationMap S sbar RshS) =
      pullback.snd f sbar.hom ≫ iS := sorry

/-- The geometric-fibre comparison is the pullback of
`Spec(κ(s̄)) ⟶ Spec(O^{sh}_{S,s̄})` along the henselized-fibre projection. -/
theorem isPullback_geometricFiberToHenselized
    (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar RshS)
    (hiS : iS ≫ strictHenselizationMap S sbar RshS = sbar.hom) :
    IsPullback (geometricFiberToHenselized f sbar RshS iS hiS)
      (pullback.snd f sbar.hom)
      (pullback.snd f (strictHenselizationMap S sbar RshS)) iS := sorry

end AlgebraicGeometry.Scheme.Etale

end
