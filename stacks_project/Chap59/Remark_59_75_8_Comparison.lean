/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImageStalk

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

#check (AlgebraicGeometry.Scheme.Etale.geometricFiberToHenselized f sbar RshS :
  ∀ (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar RshS)
    (_ : iS ≫ strictHenselizationMap S sbar RshS = sbar.hom),
    pullback f sbar.hom ⟶ henselizedFiber f sbar RshS)

#check (AlgebraicGeometry.Scheme.Etale.geometricFiberToHenselized_comp_toX f sbar RshS :
  ∀ (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar RshS)
    (hiS : iS ≫ strictHenselizationMap S sbar RshS = sbar.hom),
    geometricFiberToHenselized f sbar RshS iS hiS ≫
        henselizedFiberToX f sbar RshS =
      pullback.fst f sbar.hom)

#check (AlgebraicGeometry.Scheme.Etale.geometricFiberToHenselized_comp_toBase f sbar RshS :
  ∀ (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar RshS)
    (hiS : iS ≫ strictHenselizationMap S sbar RshS = sbar.hom),
    geometricFiberToHenselized f sbar RshS iS hiS ≫
        pullback.snd f (strictHenselizationMap S sbar RshS) =
      pullback.snd f sbar.hom ≫ iS)

#check (AlgebraicGeometry.Scheme.Etale.isPullback_geometricFiberToHenselized f sbar RshS :
  ∀ (iS : Spec (.of sbar.K) ⟶ strictHenselizationScheme S sbar RshS)
    (hiS : iS ≫ strictHenselizationMap S sbar RshS = sbar.hom),
    IsPullback (geometricFiberToHenselized f sbar RshS iS hiS)
      (pullback.snd f sbar.hom)
      (pullback.snd f (strictHenselizationMap S sbar RshS)) iS)

end AlgebraicGeometry.Scheme.Etale

end
