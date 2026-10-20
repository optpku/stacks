/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.FiniteLimits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.Limits

/-!
# Limits in chosen pro-étale sites

Typed checks retain the source-facing import surface for chosen pro-étale limits.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

variable (X : AlgebraicGeometry.ChosenBigProetaleSite.{u, v}) (S : X.carrier)

#check (AlgebraicGeometry.ChosenBigProetaleSite.smallSiteHasPullbacks X S :
  HasPullbacks (AlgebraicGeometry.ChosenBigProetaleSite.smallSite X S))

#check (AlgebraicGeometry.ChosenBigProetaleSite.smallSiteHasEqualizers X S :
  HasEqualizers (AlgebraicGeometry.ChosenBigProetaleSite.smallSite X S))

#check (AlgebraicGeometry.ChosenBigProetaleSite.bigSiteHasEqualizers X S :
  HasEqualizers (AlgebraicGeometry.ChosenBigProetaleSite.bigSite X S))

#check (AlgebraicGeometry.ChosenBigProetaleSite.smallTerminalObjectIsTerminal X S :
  IsTerminal (AlgebraicGeometry.ChosenBigProetaleSite.smallTerminalObject X S))

namespace AlgebraicGeometry.ChosenBigProetaleSite

/-- The identity object is terminal in the chosen big pro-étale slice over `S`. -/
noncomputable def bigSiteIdentityTerminal (X : ChosenBigProetaleSite.{u, v})
    (S : X.carrier) :
    IsTerminal (Over.mk (𝟙 S) : bigSite X S) :=
  AlgebraicGeometry.ChosenBigSite.sliceIdentityTerminal X S

end AlgebraicGeometry.ChosenBigProetaleSite
