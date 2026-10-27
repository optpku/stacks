/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints

/-! # Finite-family excision by elementary étale neighbourhoods -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- Base change along affine elementary étale neighbourhoods of distinct closed points
of a decent algebraic space, with singleton inverse images of the selected finite range,
defines a functor from morphisms that are isomorphisms off that range to families of
morphisms that are isomorphisms off the distinguished neighbourhood points. -/
def excisionFamilyFunctor {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U) :
    IsoOverClosedPoints X x hx ⥤
      ∀ i, IsoOverOpen (closedPointComplementι (ofOver ((U i).toOver))
        (isClosed_neighborhoodPoint X x hx U hU i)) :=
  Functor.pi' fun i ↦ ObjectProperty.lift
    (isoOverOpenProperty (closedPointComplementι (ofOver ((U i).toOver))
      (isClosed_neighborhoodPoint X x hx U hU i)))
    (IsoOverOpen.inclusion (closedPointsComplementι X x hx) ⋙
      overPullback (U i).hom)
    (fun Y ↦ (isIsoOverOpen_openInverseImage_iff_closedPointComplement
      X x hx U hU i (isClosed_neighborhoodPoint X x hx U hU i)
      ((overPullback (U i).hom).obj Y.obj).hom).mp
      (IsoOverOpen.baseChange_mem (U i).hom (closedPointsComplementι X x hx) Y))

/-- Each coordinate of the excision functor has the same underlying base-change object as the
general inverse-image functor `IsoOverClosedPoints.baseChangeFamily`. -/
theorem excisionFamilyFunctor_eq {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx) (i : ι) :
    ((excisionFamilyFunctor X x hx hx_inj U hU_affine hU_elem hU).obj Y i).obj =
      ((IsoOverClosedPoints.baseChangeFamily X x hx U).obj Y i).obj :=
  sorry

/-- Base change along affine elementary étale neighbourhoods of distinct closed points
of a decent algebraic space is faithful on morphisms that are isomorphisms away from
the selected points, when each neighbourhood meets that finite range only at its
distinguished point. -/
instance excisionFamilyFunctor_faithful {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U) :
    (excisionFamilyFunctor X x hx hx_inj U hU_affine hU_elem hU).Faithful :=
  sorry

/-- Base change along affine elementary étale neighbourhoods of distinct closed points
of a decent algebraic space is full on morphisms that are isomorphisms away from
the selected points, when each neighbourhood meets that finite range only at its
distinguished point. -/
instance excisionFamilyFunctor_full {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U) :
    (excisionFamilyFunctor X x hx hx_inj U hU_affine hU_elem hU).Full :=
  sorry

/-- Every family of morphisms that are isomorphisms away from the distinguished points
of affine elementary étale neighbourhoods of distinct closed points of a decent
algebraic space arises, up to isomorphism, by base change of a morphism that is an
isomorphism away from the selected points, provided each neighbourhood meets the
selected finite range only at its distinguished point. -/
instance excisionFamilyFunctor_essSurj {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U) :
    (excisionFamilyFunctor X x hx hx_inj U hU_affine hU_elem hU).EssSurj :=
  sorry

/-- Base change along affine elementary étale neighbourhoods of distinct closed points
of a decent algebraic space gives an equivalence between morphisms that are
isomorphisms away from the selected finite range and families of morphisms that are
isomorphisms away from the distinguished neighbourhood points, provided each
neighbourhood meets the selected range only at its distinguished point. -/
@[stacks 0BHB]
instance excisionFamilyFunctor_isEquivalence {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U) :
    (excisionFamilyFunctor X x hx hx_inj U hU_affine hU_elem hU).IsEquivalence where
  faithful := excisionFamilyFunctor_faithful X x hx hx_inj U hU_affine hU_elem hU
  full := excisionFamilyFunctor_full X x hx hx_inj U hU_affine hU_elem hU
  essSurj := excisionFamilyFunctor_essSurj X x hx hx_inj U hU_affine hU_elem hU

end AlgebraicGeometry.AlgebraicSpace
