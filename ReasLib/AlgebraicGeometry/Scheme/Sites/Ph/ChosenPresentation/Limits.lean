module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.ChosenPresentation

/-!
# Pullbacks in chosen big ph sites

This file records pullback and terminal-object properties of chosen big ph
site presentations and their affine-source subcategories.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigPhSite

variable (X : ChosenBigPhSite.{u, v}) (S : X.carrier)

/-- Affine-source objects of a chosen big ph slice are closed under
pullbacks. -/
theorem bigAffineObjectsIsClosedUnderPullbacks :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (bigAffineObjects X S) Limits.WalkingCospan := sorry

/-- A chosen big affine ph carrier has pullbacks. -/
theorem bigAffineSiteHasPullbacks :
    Limits.HasPullbacks (bigAffineSite X S) := sorry

/-- The source-scheme functor from a chosen big affine ph carrier preserves
pullbacks. -/
theorem bigAffineToSchemePreservesPullbacks :
    Limits.PreservesLimitsOfShape Limits.WalkingCospan
      (bigAffineToScheme X S) := sorry

/-- The identity object `S/S` is terminal in a chosen big ph slice. -/
noncomputable def bigSiteIdentityTerminal :
    Limits.IsTerminal (Over.mk (𝟙 S) : bigSite X S) :=
  Over.mkIdTerminal

end AlgebraicGeometry.ChosenBigPhSite
