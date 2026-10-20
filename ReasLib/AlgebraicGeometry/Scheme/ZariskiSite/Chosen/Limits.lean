module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Zariski.Affine

/-!
# Pullbacks in chosen Zariski sites

This file records pullback and terminal-object properties of the canonical
chosen big, small, big-affine, and small-affine Zariski carriers.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigZariskiSite

variable (𝒮 : ChosenBigZariskiSite.{u, v}) (S : 𝒮.carrier)

/-- The carrier of a chosen big Zariski presentation has pullbacks. -/
theorem carrierHasPullbacks : Limits.HasPullbacks 𝒮.carrier :=
  𝒮.hasPullbacks

/-- The canonical chosen big Zariski slice has pullbacks. -/
theorem bigSiteHasPullbacks : Limits.HasPullbacks (bigSite 𝒮 S) :=
  ChosenBigSite.sliceHasPullbacks 𝒮 S

/-- The source-scheme functor from the canonical chosen big Zariski slice
preserves pullbacks. -/
theorem bigToSchemePreservesPullbacks :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan (bigToScheme 𝒮 S) :=
  ChosenBigSite.sliceToSchemePreservesPullbacks 𝒮 S

/-- Affine-source objects of the canonical chosen big Zariski slice are closed
under pullbacks. -/
theorem bigAffineObjectsIsClosedUnderPullbacks :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (bigAffineObjects 𝒮 S) Limits.WalkingCospan := sorry

/-- The canonical chosen big affine Zariski carrier has pullbacks. -/
theorem bigAffineSiteHasPullbacks :
    Limits.HasPullbacks (bigAffineSite 𝒮 S) := sorry

/-- The source-scheme functor from the canonical chosen big affine Zariski
carrier preserves pullbacks. -/
theorem bigAffineToSchemePreservesPullbacks :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (bigAffineToScheme 𝒮 S) := sorry

/-- The canonical chosen small Zariski carrier has pullbacks. -/
theorem smallSiteHasPullbacks : Limits.HasPullbacks (smallSite 𝒮 S) := sorry

/-- The source-scheme functor from the canonical chosen small Zariski carrier
preserves pullbacks. -/
theorem smallToSchemePreservesPullbacks :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (smallToScheme 𝒮 S) := sorry

/-- Affine-source objects of the canonical chosen small Zariski carrier are
closed under pullbacks. -/
theorem smallAffineObjectsIsClosedUnderPullbacks :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (smallAffineObjects 𝒮 S) Limits.WalkingCospan := sorry

/-- The canonical chosen small affine Zariski carrier has pullbacks. -/
theorem smallAffineSiteHasPullbacks :
    Limits.HasPullbacks (smallAffineSite 𝒮 S) := sorry

/-- The source-scheme functor from the canonical chosen small affine Zariski
carrier preserves pullbacks. -/
theorem smallAffineToSchemePreservesPullbacks :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (smallAffineToScheme 𝒮 S) := sorry

/-- The identity object `S/S` is terminal in the canonical chosen big Zariski
slice. -/
noncomputable def bigSiteIdentityTerminal :
    Limits.IsTerminal (Over.mk (𝟙 S) : bigSite 𝒮 S) :=
  Over.mkIdTerminal

/-- The identity object `S/S` as an object of the canonical chosen small
Zariski carrier. -/
def smallTerminalObject : smallSite 𝒮 S :=
  ⟨Over.mk (𝟙 S), by
    change IsOpenImmersion (𝒮.toScheme.map (𝟙 S))
    exact (𝒮.toScheme.map_id S).symm ▸
      (inferInstance : IsOpenImmersion (𝟙 (𝒮.toScheme.obj S)))⟩

/-- The canonical morphism from a chosen small Zariski object to `S/S`. -/
def smallTerminalFrom (X : smallSite 𝒮 S) :
    X ⟶ smallTerminalObject 𝒮 S :=
  ObjectProperty.homMk (Over.homMk X.obj.hom (by
    change X.obj.hom ≫ 𝟙 S = X.obj.hom
    exact Category.comp_id _))

/-- Every morphism from a chosen small Zariski object to `S/S` is the
canonical one. -/
theorem smallTerminalFrom_unique (X : smallSite 𝒮 S)
    (f : X ⟶ smallTerminalObject 𝒮 S) :
    f = smallTerminalFrom 𝒮 S X := sorry

/-- The identity object `S/S` is terminal in the canonical chosen small
Zariski carrier. -/
noncomputable def smallTerminalObjectIsTerminal :
    Limits.IsTerminal (smallTerminalObject 𝒮 S) :=
  Limits.IsTerminal.ofUniqueHom (smallTerminalFrom 𝒮 S)
    (smallTerminalFrom_unique 𝒮 S)

end AlgebraicGeometry.ChosenBigZariskiSite
