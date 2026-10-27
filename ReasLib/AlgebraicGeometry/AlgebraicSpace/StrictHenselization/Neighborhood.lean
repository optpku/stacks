/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.AlgebraicGeometry.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Neighborhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Henselization.Map

/-!
# Strict henselizations presented by étale neighbourhoods

A small étale neighbourhood presents the strict henselization at its induced
geometric point. Its canonical structural morphism determines a morphism to the
algebraic space, a closed point, and closed fibres after base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {Y : AlgebraicSpace S} {ybar : GeometricPoint Y}

/-- The étale local ring of the neighbourhood scheme at the induced geometric point. -/
abbrev neighborhoodEtaleLocalRing (N : SmallEtaleNeighborhood ybar) : Type u :=
  Scheme.etaleLocalRing.asCommRing N.toSite.left.left
    (GeometricPoint.SmallEtaleNeighborhood.schemeGeometricPoint N)

/-- `neighborhoodEtaleLocalRing N` is the scheme-theoretic étale local ring of `N`
at `schemeGeometricPoint N`. -/
theorem neighborhoodEtaleLocalRing_eq (N : SmallEtaleNeighborhood ybar) :
    neighborhoodEtaleLocalRing N =
      Scheme.etaleLocalRing N.toSite.left.left
        (GeometricPoint.SmallEtaleNeighborhood.schemeGeometricPoint N) := by
  rfl

/-- The étale local ring of a neighbourhood scheme is local. -/
instance neighborhoodEtaleLocalRing.isLocalRing (N : SmallEtaleNeighborhood ybar) :
    IsLocalRing (neighborhoodEtaleLocalRing N) :=
  (@Scheme.Etale.stalkRing.isStrictHenselizationOf N.toSite.left.left
      (GeometricPoint.SmallEtaleNeighborhood.schemeGeometricPoint N).K inferInstance
      (@IsSepClosed.of_isAlgClosed
        (GeometricPoint.SmallEtaleNeighborhood.schemeGeometricPoint N).K inferInstance
        (GeometricPoint.SmallEtaleNeighborhood.schemeGeometricPoint N).isAlgClosed)
      (GeometricPoint.SmallEtaleNeighborhood.schemeGeometricPoint N).hom).toStrictHenselianLocalRing.toHenselianLocalRing.toIsLocalRing

/-- The structure morphism `Spec(𝒪_{N, ū}^{et}) ⟶ S` obtained by composing the
neighbourhood factorization with the structure morphism of `N` over `S`. -/
def strictHenselizationToBaseOf (N : SmallEtaleNeighborhood ybar) :
    Spec (CommRingCat.of (neighborhoodEtaleLocalRing N)) ⟶ S :=
  Scheme.StrictHenselization.toScheme N.toSite.left.left
    (GeometricPoint.SmallEtaleNeighborhood.schemeGeometricPoint N) ≫ N.toSite.left.hom

/-- `strictHenselizationToBaseOf N` is the composite through the neighbourhood
scheme. -/
theorem strictHenselizationToBaseOf_eq (N : SmallEtaleNeighborhood ybar) :
    strictHenselizationToBaseOf N =
      Scheme.StrictHenselization.toScheme N.toSite.left.left
        (GeometricPoint.SmallEtaleNeighborhood.schemeGeometricPoint N) ≫ N.toSite.left.hom := by
  rfl

/-- The strict henselization of `Y` at `ybar`, presented along `N` as a scheme over
`S`. -/
def strictHenselizationOverOf (N : SmallEtaleNeighborhood ybar) : Over S :=
  Over.mk (strictHenselizationToBaseOf N)

/-- The underlying scheme of `strictHenselizationOverOf N` is
`Spec(neighborhoodEtaleLocalRing N)`. -/
theorem strictHenselizationOverOf_left (N : SmallEtaleNeighborhood ybar) :
    (strictHenselizationOverOf N).left =
      Spec (CommRingCat.of (neighborhoodEtaleLocalRing N)) := by
  rfl

/-- The structure morphism of `strictHenselizationOverOf N` is
`strictHenselizationToBaseOf N`. -/
theorem strictHenselizationOverOf_hom (N : SmallEtaleNeighborhood ybar) :
    (strictHenselizationOverOf N).hom = strictHenselizationToBaseOf N := by
  rfl

/-- The morphism `Y^{sh} ⟶ Y` of algebraic spaces over `S` associated to a small
étale neighbourhood of `ybar`. -/
def strictHenselizationHomOf (N : SmallEtaleNeighborhood ybar) :
    ofOver (strictHenselizationOverOf N) ⟶ Y :=
  ofOverMap (Over.homMk (Scheme.StrictHenselization.toScheme N.toSite.left.left
    (GeometricPoint.SmallEtaleNeighborhood.schemeGeometricPoint N)) rfl) ≫ N.toSite.hom

/-- `strictHenselizationHomOf N` factors as the neighbourhood scheme map followed
by `N ⟶ Y`. -/
theorem strictHenselizationHomOf_spec (N : SmallEtaleNeighborhood ybar) :
    strictHenselizationHomOf N =
      ofOverMap (Over.homMk (Scheme.StrictHenselization.toScheme N.toSite.left.left
        (GeometricPoint.SmallEtaleNeighborhood.schemeGeometricPoint N)) rfl) ≫
        N.toSite.hom := by
  rfl

/-- The closed point of `Y^{sh}` presented along `N`. -/
def closedPoint (N : SmallEtaleNeighborhood ybar) :
    Spec (CommRingCat.of (neighborhoodEtaleLocalRing N)) :=
  IsLocalRing.closedPoint (neighborhoodEtaleLocalRing N)

/-- `closedPoint N` is the closed point of the local ring
`neighborhoodEtaleLocalRing N`. -/
theorem closedPoint_eq (N : SmallEtaleNeighborhood ybar) :
    closedPoint N = IsLocalRing.closedPoint (neighborhoodEtaleLocalRing N) := by
  rfl

/-- The image of the closed point of `Y^{sh}` under `strictHenselizationHomOf N`
is the image of `ybar` in `|Y|`. -/
theorem strictHenselizationHomOf_map_closedPoint (N : SmallEtaleNeighborhood ybar) :
    Points.map (strictHenselizationHomOf N)
        (ofOver.pointsEquiv (strictHenselizationOverOf N) (closedPoint N)) =
      ybar.image :=
  sorry

variable {X : AlgebraicSpace S}

/-- The closed fibre of `X^{sh}` over `closedPoint N`. -/
def closedFiber (f : X ⟶ Y) (N : SmallEtaleNeighborhood ybar) :
    Set (Points (Limits.pullback f (strictHenselizationHomOf N))) :=
  Points.map (Limits.pullback.snd f (strictHenselizationHomOf N)) ⁻¹'
    {ofOver.pointsEquiv (strictHenselizationOverOf N) (closedPoint N)}

/-- A point of `X^{sh}` lies on the closed fibre if and only if it maps to
`closedPoint N` in `Y^{sh}`. -/
theorem closedFiber_mem_iff (f : X ⟶ Y) (N : SmallEtaleNeighborhood ybar)
    (ξ : Points (Limits.pullback f (strictHenselizationHomOf N))) :
    ξ ∈ closedFiber f N ↔
      Points.map (Limits.pullback.snd f (strictHenselizationHomOf N)) ξ =
        ofOver.pointsEquiv (strictHenselizationOverOf N) (closedPoint N) := by
  rfl

end AlgebraicGeometry.AlgebraicSpace
