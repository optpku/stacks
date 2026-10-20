module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjunction for the represented-scheme étale-site comparison

Module direct image along the comparison from a represented algebraic space's
small étale site to its representing scheme's small étale site admits a left adjoint.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Module direct image along the represented-scheme étale-site comparison
admits a left adjoint. -/
instance instIsRightAdjoint_schemeEtaleRingedHom_modulePushforward
    {S : Scheme.{u}} (U : Over S) :
    ((schemeEtaleRingedHom U).modulePushforward.{u}).IsRightAdjoint :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
