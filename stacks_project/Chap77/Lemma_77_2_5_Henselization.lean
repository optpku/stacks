/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.AlgebraicGeometry.Stalk
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_19_6_Neighborhood
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_29_2_Pullback

/-!
# Canonical morphism from a strict henselization

A geometric point `ybar` of an algebraic space `Y` and a small étale neighbourhood
`N` of `ybar` determine the strict henselization of the neighbourhood scheme at
the induced geometric point. The Zariski-to-étale comparison and `fromSpecStalk`
assemble a morphism `Y^{sh} ⟶ Y` over `S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtaleNeighborhood

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {Y : AlgebraicSpace S} {ybar : GeometricPoint Y}

/-- The geometric point of the represented neighbourhood space `ofOver N.toSite.left`
induced by the chosen lift of `ybar`. -/
def spaceGeometricPoint (N : SmallEtaleNeighborhood ybar) :
    GeometricPoint (ofOver N.toSite.left) where
  K := ybar.K
  structureHom := ybar.structureHom
  hom := N.lift
  isAlgClosed := ybar.isAlgClosed

/-- The underlying field of `spaceGeometricPoint N` is the source field of `ybar`. -/
theorem spaceGeometricPoint_K (N : SmallEtaleNeighborhood ybar) :
    (spaceGeometricPoint N).K = ybar.K :=
  sorry

/-- The algebraic-space morphism of `spaceGeometricPoint N` is the chosen lift. -/
theorem spaceGeometricPoint_hom (N : SmallEtaleNeighborhood ybar) :
    (spaceGeometricPoint N).hom = N.lift :=
  sorry

/-- The geometric point of the neighbourhood scheme induced by the chosen lift of
`ybar`. -/
def schemeGeometricPoint (N : SmallEtaleNeighborhood ybar) :
    Scheme.GeometricPoint N.toSite.left.left :=
  GeometricPoint.toScheme (spaceGeometricPoint N)

/-- Recovering the scheme geometric point of `spaceGeometricPoint N` yields
`schemeGeometricPoint N`. -/
theorem schemeGeometricPoint_eq (N : SmallEtaleNeighborhood ybar) :
    schemeGeometricPoint N = GeometricPoint.toScheme (spaceGeometricPoint N) :=
  sorry

/-- The center of the neighbourhood geometric point, as a point of the neighbourhood
scheme. -/
def center (N : SmallEtaleNeighborhood ybar) : N.toSite.left.left :=
  (schemeGeometricPoint N).image

/-- The center of an étale neighbourhood is the image of its scheme geometric point. -/
theorem center_eq_image (N : SmallEtaleNeighborhood ybar) :
    center N = (schemeGeometricPoint N).image :=
  sorry

/-- The étale local ring of the neighbourhood scheme at the induced geometric point. -/
abbrev neighborhoodEtaleLocalRing (N : SmallEtaleNeighborhood ybar) : Type u :=
  Scheme.etaleLocalRing N.toSite.left.left (schemeGeometricPoint N)

/-- `neighborhoodEtaleLocalRing N` is the scheme-theoretic étale local ring of `N`
at `schemeGeometricPoint N`. -/
theorem neighborhoodEtaleLocalRing_eq (N : SmallEtaleNeighborhood ybar) :
    neighborhoodEtaleLocalRing N =
      Scheme.etaleLocalRing N.toSite.left.left (schemeGeometricPoint N) :=
  sorry

/-- The étale local ring of a neighbourhood scheme is a commutative ring. -/
instance neighborhoodEtaleLocalRing.commRing (N : SmallEtaleNeighborhood ybar) :
    CommRing (neighborhoodEtaleLocalRing N) :=
  Scheme.etaleLocalRing.commRing N.toSite.left.left (schemeGeometricPoint N)

/-- The étale local ring of a neighbourhood scheme is local. -/
instance neighborhoodEtaleLocalRing.isLocalRing (N : SmallEtaleNeighborhood ybar) :
    IsLocalRing (neighborhoodEtaleLocalRing N) :=
  (Scheme.etaleLocalRing.instIsStrictHenselizationOf N.toSite.left.left
      (schemeGeometricPoint N)).toStrictHenselianLocalRing.toHenselianLocalRing.toIsLocalRing

/-- Canonical comparison from the Zariski stalk of the neighbourhood scheme at the
center to the étale local ring of that scheme. -/
def neighborhoodFromZariskiStalk (N : SmallEtaleNeighborhood ybar) :
    N.toSite.left.left.presheaf.stalk (schemeGeometricPoint N).image →+*
      neighborhoodEtaleLocalRing N :=
  Scheme.etaleLocalRing.fromZariskiStalk N.toSite.left.left (schemeGeometricPoint N)

/-- `neighborhoodFromZariskiStalk N` is the scheme-level Zariski-to-étale comparison. -/
theorem neighborhoodFromZariskiStalk_eq (N : SmallEtaleNeighborhood ybar) :
    neighborhoodFromZariskiStalk N =
      Scheme.etaleLocalRing.fromZariskiStalk N.toSite.left.left
        (schemeGeometricPoint N) :=
  sorry

/-- The scheme morphism `Spec(𝒪_{N, ū}^{et}) ⟶ N` induced by the Zariski-to-étale
comparison along a small étale neighbourhood of `ybar`. -/
def strictHenselizationToNeighborhoodOf (N : SmallEtaleNeighborhood ybar) :
    Spec (CommRingCat.of (neighborhoodEtaleLocalRing N)) ⟶ N.toSite.left.left :=
  Spec.map (CommRingCat.ofHom (neighborhoodFromZariskiStalk N)) ≫
    N.toSite.left.left.fromSpecStalk (schemeGeometricPoint N).image

/-- `strictHenselizationToNeighborhoodOf N` is `Spec.map` of
`neighborhoodFromZariskiStalk N` followed by `fromSpecStalk` at the centre of
`N`. -/
theorem strictHenselizationToNeighborhoodOf_eq (N : SmallEtaleNeighborhood ybar) :
    strictHenselizationToNeighborhoodOf N =
      Spec.map (CommRingCat.ofHom (neighborhoodFromZariskiStalk N)) ≫
        N.toSite.left.left.fromSpecStalk (schemeGeometricPoint N).image :=
  sorry

/-- The structure morphism `Spec(𝒪_{N, ū}^{et}) ⟶ S` obtained by composing the
neighbourhood factorization with the structure morphism of `N` over `S`. -/
def strictHenselizationToBaseOf (N : SmallEtaleNeighborhood ybar) :
    Spec (CommRingCat.of (neighborhoodEtaleLocalRing N)) ⟶ S :=
  strictHenselizationToNeighborhoodOf N ≫ N.toSite.left.hom

/-- `strictHenselizationToBaseOf N` is the composite through the neighbourhood
scheme. -/
theorem strictHenselizationToBaseOf_eq (N : SmallEtaleNeighborhood ybar) :
    strictHenselizationToBaseOf N =
      strictHenselizationToNeighborhoodOf N ≫ N.toSite.left.hom :=
  sorry

/-- The strict henselization of `Y` at `ybar`, presented along `N` as a scheme over
`S`. -/
def strictHenselizationOverOf (N : SmallEtaleNeighborhood ybar) : Over S :=
  Over.mk (strictHenselizationToBaseOf N)

/-- The underlying scheme of `strictHenselizationOverOf N` is
`Spec(neighborhoodEtaleLocalRing N)`. -/
theorem strictHenselizationOverOf_left (N : SmallEtaleNeighborhood ybar) :
    (strictHenselizationOverOf N).left =
      Spec (CommRingCat.of (neighborhoodEtaleLocalRing N)) :=
  sorry

/-- The structure morphism of `strictHenselizationOverOf N` is
`strictHenselizationToBaseOf N`. -/
theorem strictHenselizationOverOf_hom (N : SmallEtaleNeighborhood ybar) :
    (strictHenselizationOverOf N).hom = strictHenselizationToBaseOf N :=
  sorry

/-- Compatibility of `strictHenselizationToNeighborhoodOf N` with the structure
morphism of `N` over `S`. -/
theorem strictHenselizationToNeighborhoodOf_w (N : SmallEtaleNeighborhood ybar) :
    strictHenselizationToNeighborhoodOf N ≫ N.toSite.left.hom =
      (strictHenselizationOverOf N).hom :=
  sorry

/-- The morphism `Y^{sh} ⟶ Y` of algebraic spaces over `S` associated to a small
étale neighbourhood of `ybar`. -/
def strictHenselizationHomOf (N : SmallEtaleNeighborhood ybar) :
    ofOver (strictHenselizationOverOf N) ⟶ Y :=
  ofOverMap (Over.homMk (strictHenselizationToNeighborhoodOf N) rfl) ≫ N.toSite.hom

/-- `strictHenselizationHomOf N` factors as the neighbourhood scheme map followed
by `N ⟶ Y`. -/
theorem strictHenselizationHomOf_spec (N : SmallEtaleNeighborhood ybar) :
    strictHenselizationHomOf N =
      ofOverMap (Over.homMk (strictHenselizationToNeighborhoodOf N) rfl) ≫
        N.toSite.hom :=
  sorry

/-- The closed point of `Y^{sh}` presented along `N`. -/
def closedPoint (N : SmallEtaleNeighborhood ybar) :
    Spec (CommRingCat.of (neighborhoodEtaleLocalRing N)) :=
  IsLocalRing.closedPoint (neighborhoodEtaleLocalRing N)

/-- `closedPoint N` is the closed point of the local ring
`neighborhoodEtaleLocalRing N`. -/
theorem closedPoint_eq (N : SmallEtaleNeighborhood ybar) :
    closedPoint N = IsLocalRing.closedPoint (neighborhoodEtaleLocalRing N) :=
  sorry

/-- The image of the closed point of `Y^{sh}` under `strictHenselizationHomOf N`
is the image of `ybar` in `|Y|`. -/
theorem strictHenselizationHomOf_map_closedPoint (N : SmallEtaleNeighborhood ybar) :
    Points.map (strictHenselizationHomOf N)
        (ofOver.pointsEquiv (strictHenselizationOverOf N) (closedPoint N)) =
      ybar.image :=
  sorry

variable {X : AlgebraicSpace S}

/-- The projection `X^{sh} ⟶ Y^{sh}` of the pullback of `X` along
`strictHenselizationHomOf N`. -/
def pullbackHom (f : X ⟶ Y) (N : SmallEtaleNeighborhood ybar) :
    Limits.pullback f (strictHenselizationHomOf N) ⟶
      ofOver (strictHenselizationOverOf N) :=
  Limits.pullback.snd f (strictHenselizationHomOf N)

/-- `pullbackHom f N` is the second projection of the pullback along
`strictHenselizationHomOf N`. -/
theorem pullbackHom_eq (f : X ⟶ Y) (N : SmallEtaleNeighborhood ybar) :
    pullbackHom f N = Limits.pullback.snd f (strictHenselizationHomOf N) :=
  sorry

/-- The closed fibre of `X^{sh}` over `closedPoint N`. -/
def closedFiber (f : X ⟶ Y) (N : SmallEtaleNeighborhood ybar) :
    Set (Points (Limits.pullback f (strictHenselizationHomOf N))) :=
  Points.map (pullbackHom f N) ⁻¹'
    {ofOver.pointsEquiv (strictHenselizationOverOf N) (closedPoint N)}

/-- A point of `X^{sh}` lies on the closed fibre if and only if it maps to
`closedPoint N` in `Y^{sh}`. -/
theorem closedFiber_mem_iff (f : X ⟶ Y) (N : SmallEtaleNeighborhood ybar)
    (ξ : Points (Limits.pullback f (strictHenselizationHomOf N))) :
    ξ ∈ closedFiber f N ↔
      Points.map (pullbackHom f N) ξ =
        ofOver.pointsEquiv (strictHenselizationOverOf N) (closedPoint N) :=
  sorry

namespace Modules

/-- The pullback of an `𝒪_X`-module to `X^{sh} = X ×_Y Y^{sh}`. -/
def pullbackModules (F : X.Modules) (f : X ⟶ Y) (N : SmallEtaleNeighborhood ybar) :
    (Limits.pullback f (strictHenselizationHomOf N)).Modules :=
  (pullback (Limits.pullback.fst f (strictHenselizationHomOf N))).obj F

/-- `pullbackModules F f N` is the module pullback of `F` along the first
projection of `X^{sh}`. -/
theorem pullbackModules_eq (F : X.Modules) (f : X ⟶ Y)
    (N : SmallEtaleNeighborhood ybar) :
    pullbackModules F f N =
      (pullback (Limits.pullback.fst f (strictHenselizationHomOf N))).obj F :=
  sorry

end Modules

end AlgebraicGeometry.AlgebraicSpace

