module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.ChosenPresentation

/-!
# Pullbacks in chosen big fppf sites

This file records pullback and terminal-object properties of chosen big fppf
site presentations and their affine-source subcategories.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

variable (X : ChosenBigFppfSite.{u, v}) (S : X.carrier)

/-- A chosen big fppf carrier has pullbacks. -/
theorem carrierHasPullbacks : Limits.HasPullbacks X.carrier :=
  X.hasPullbacks

/-- Affine-source objects of a chosen big fppf slice are closed under
pullbacks. -/
theorem bigAffineObjectsIsClosedUnderPullbacks :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (bigAffineObjects X S) Limits.WalkingCospan := sorry

/-- A chosen big affine fppf carrier has pullbacks. -/
theorem bigAffineSiteHasPullbacks :
    Limits.HasPullbacks (bigAffineSite X S) := sorry

/-- The source-scheme functor from a chosen big affine fppf carrier preserves
pullbacks. -/
theorem bigAffineToSchemePreservesPullbacks :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (bigAffineToScheme X S) := sorry

/-- The identity object `S/S` is terminal in a chosen big fppf slice. -/
noncomputable def bigSiteIdentityTerminal :
    Limits.IsTerminal (Over.mk (𝟙 S) : bigSite X S) :=
  Over.mkIdTerminal

end AlgebraicGeometry.ChosenBigFppfSite
