/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ChosenPresentation.Affine

/-!
# Pullbacks in chosen étale sites

This file records pullback and terminal-object properties of the canonical
chosen small, big-affine, and small-affine étale carriers.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigEtaleSite

variable (X : ChosenBigEtaleSite.{u, v}) (S : X.carrier)

/-- The carrier of a chosen big étale presentation has pullbacks. -/
theorem carrierHasPullbacks : Limits.HasPullbacks X.carrier :=
  X.hasPullbacks

/-- Étale objects of a chosen big étale slice are closed under pullbacks. -/
theorem smallObjectsIsClosedUnderPullbacks :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (smallObjects X S) Limits.WalkingCospan := sorry

/-- The canonical chosen small étale carrier has pullbacks. -/
theorem smallSiteHasPullbacks : Limits.HasPullbacks (smallSite X S) := sorry

/-- The source-scheme functor from the canonical chosen small étale carrier
preserves pullbacks. -/
theorem smallToSchemePreservesPullbacks :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (smallToScheme X S) := sorry

/-- Affine-source objects of the canonical chosen big étale slice are closed
under pullbacks. -/
theorem bigAffineObjectsIsClosedUnderPullbacks :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (bigAffineObjects X S) Limits.WalkingCospan := sorry

/-- The canonical chosen big affine étale carrier has pullbacks. -/
theorem bigAffineSiteHasPullbacks :
    Limits.HasPullbacks (bigAffineSite X S) := sorry

/-- The source-scheme functor from the canonical chosen big affine étale
carrier preserves pullbacks. -/
theorem bigAffineToSchemePreservesPullbacks :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (bigAffineToScheme X S) := sorry

/-- Affine-source objects of the canonical chosen small étale carrier are
closed under pullbacks. -/
theorem smallAffineObjectsIsClosedUnderPullbacks :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (smallAffineObjects X S) Limits.WalkingCospan := sorry

/-- The canonical chosen small affine étale carrier has pullbacks. -/
theorem smallAffineSiteHasPullbacks :
    Limits.HasPullbacks (smallAffineSite X S) := sorry

/-- The source-scheme functor from the canonical chosen small affine étale
carrier preserves pullbacks. -/
theorem smallAffineToSchemePreservesPullbacks :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (smallAffineToScheme X S) := sorry

/-- The identity object `S/S` is terminal in the canonical chosen big étale
slice. -/
noncomputable def bigSiteIdentityTerminal :
    Limits.IsTerminal (Over.mk (𝟙 S) : bigSite X S) :=
  Over.mkIdTerminal

/-- The identity object `S/S` as an object of the canonical chosen small
étale carrier. -/
def smallTerminalObject : smallSite X S :=
  ⟨Over.mk (𝟙 S), by
    change Etale (X.toScheme.map (𝟙 S))
    exact (X.toScheme.map_id S).symm ▸
      (inferInstance : Etale (𝟙 (X.toScheme.obj S)))⟩

/-- The canonical morphism from a chosen small étale object to `S/S`. -/
def smallTerminalFrom (U : smallSite X S) :
    U ⟶ smallTerminalObject X S :=
  ObjectProperty.homMk (Over.homMk U.obj.hom (by
    change U.obj.hom ≫ 𝟙 S = U.obj.hom
    exact Category.comp_id _))

/-- Every morphism from a chosen small étale object to `S/S` is the
canonical one. -/
theorem smallTerminalFrom_unique (U : smallSite X S)
    (f : U ⟶ smallTerminalObject X S) :
    f = smallTerminalFrom X S U := sorry

/-- The identity object `S/S` is terminal in the canonical chosen small
étale carrier. -/
noncomputable def smallTerminalObjectIsTerminal :
    Limits.IsTerminal (smallTerminalObject X S) :=
  Limits.IsTerminal.ofUniqueHom (smallTerminalFrom X S)
    (smallTerminalFrom_unique X S)

end AlgebraicGeometry.ChosenBigEtaleSite
