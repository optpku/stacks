/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Data.Finite.Defs
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Sets.Closeds
public import stacks_project.Chap66.Definition_66_12_5_Reduced
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap68.Definition_68_11_5_Neighborhood
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap70.Lemma_70_19_1_BaseChange
public import stacks_project.Chap70.Lemma_70_19_1_IsoOverOpen
public import stacks_project.Chap70.Lemma_70_19_3_Henselization

/-!
# Iso-over-open categories at a finite family of closed points

The open complement of a finite family of closed points of an algebraic space,
the corresponding iso-over-open slice category, and the Pi-assembled base-change
functor along a family of étale neighbourhoods.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {ι : Type} [Finite ι] {S : Scheme.{u}}

/-- The range of a finite family of closed points is a closed subset of `Points X`. -/
theorem isClosed_range_closedPoints (X : AlgebraicSpace S) (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) : IsClosed (Set.range x) :=
  sorry

/-- The finite set `{x i}` of closed points, as a closed subset of `Points X`. -/
def closedPointsRange (X : AlgebraicSpace S) (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) : Closeds (Points X) :=
  ⟨Set.range x, isClosed_range_closedPoints X x hx⟩

/-- The inclusion of the reduced closed subspace supported on `{x i}` is a closed
immersion. -/
instance instIsClosedImmersion_closedPointsSubspaceι (X : AlgebraicSpace S)
    (x : ι → Points X) (hx : ∀ i, x i ∈ closedPoints (Points X)) :
    IsClosedImmersion (ClosedSubspaceStructure.reduced (closedPointsRange X x hx)).ι :=
  (ClosedSubspaceStructure.reduced (closedPointsRange X x hx)).subspace.isClosedImmersion

/-- The open complement `X \ {x i}` of a finite family of closed points. -/
def closedPointsComplement (X : AlgebraicSpace S) (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) : AlgebraicSpace S :=
  closedImmersionComplement (ClosedSubspaceStructure.reduced (closedPointsRange X x hx)).ι

/-- The open immersion `X \ {x i} ⟶ X` of a finite family of closed points. -/
def closedPointsComplementι (X : AlgebraicSpace S) (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) :
    closedPointsComplement X x hx ⟶ X :=
  closedImmersionComplementι (ClosedSubspaceStructure.reduced (closedPointsRange X x hx)).ι

/-- The complement of a finite family of closed points is an open immersion into `X`. -/
instance instIsOpenImmersion_closedPointsComplementι (X : AlgebraicSpace S)
    (x : ι → Points X) (hx : ∀ i, x i ∈ closedPoints (Points X)) :
    IsOpenImmersion (closedPointsComplementι X x hx) :=
  instIsOpenImmersion_closedImmersionComplementι
    (ClosedSubspaceStructure.reduced (closedPointsRange X x hx)).ι

/-- The image of `|X \ {x i}|` in `|X|` is the complement of the finite set `{x i}`. -/
theorem closedPointsComplement_spec (X : AlgebraicSpace S) (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) :
    pointsImage (closedPointsComplementι X x hx) = (Set.range x)ᶜ :=
  sorry

/-- The category of morphisms `Y ⟶ X` that are isomorphisms over `X \ {x i}`. -/
abbrev IsoOverClosedPoints (X : AlgebraicSpace S) (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) :=
  IsoOverOpen (closedPointsComplementι X x hx)

/-- `IsoOverClosedPoints X x hx` is `IsoOverOpen` of the complement of `{x i}`. -/
theorem isoOverClosedPoints_eq (X : AlgebraicSpace S) (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) :
    IsoOverClosedPoints X x hx = IsoOverOpen (closedPointsComplementι X x hx) :=
  sorry

/-- Membership in `IsoOverClosedPoints X x hx` is `IsIsoOverOpen` over
`X \ {x i}`. -/
theorem isoOverClosedPoints_iff (X : AlgebraicSpace S) (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) (Y : Over X) :
    isoOverOpenProperty (closedPointsComplementι X x hx) Y ↔
      IsIsoOverOpen Y.hom (closedPointsComplementι X x hx) :=
  sorry

/-- The shrinking condition that each neighbourhood `U i` meets the family `{x j}`
only at the selected point `u i`. -/
def supportedOnRange (X : AlgebraicSpace S) (x : ι → Points X)
    (U : ∀ i, EtaleNeighborhood X (x i)) : Prop :=
  ∀ i, Points.mapOfOver (U i).hom ⁻¹' Set.range x = {(U i).point}

namespace IsoOverClosedPoints

/-- Base change along a family of étale neighbourhoods, as a functor
`IsoOverClosedPoints X x hx ⥤ ∀ i, IsoOverOpen (openInverseImageι (U i).hom ...)`. -/
def baseChangeFamily (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) :
    IsoOverClosedPoints X x hx ⥤
      ∀ i, IsoOverOpen (openInverseImageι (U i).hom (closedPointsComplementι X x hx)) :=
  Functor.pi' fun i ↦
    IsoOverOpen.baseChange (U i).hom (closedPointsComplementι X x hx)

/-- Projecting `baseChangeFamily` at an index recovers base change along that
neighbourhood. -/
def baseChangeFamily_eval (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (i : ι) :
    baseChangeFamily X x hx U ⋙ Pi.eval _ i ≅
      IsoOverOpen.baseChange (U i).hom (closedPointsComplementι X x hx) :=
  Functor.pi'CompEval
    (fun j ↦ IsoOverOpen.baseChange (U j).hom (closedPointsComplementι X x hx)) i

end IsoOverClosedPoints

/-- Under the shrinking condition, the selected point of each neighbourhood is closed
in the algebraic space associated to that neighbourhood. -/
theorem isClosed_neighborhoodPoint (X : AlgebraicSpace S) [IsDecent X]
    (x : ι → Points X) (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (hU : supportedOnRange X x U) (i : ι) :
    ofOver.pointsEquiv ((U i).toOver) (U i).point ∈
      closedPoints (Points (ofOver ((U i).toOver))) :=
  sorry

/-- Under the shrinking condition, being an isomorphism over the inverse image of
`X \ {x i}` is equivalent to being an isomorphism over `U i \ {u i}`. -/
theorem isIsoOverOpen_openInverseImage_iff_closedPointComplement
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (hU : supportedOnRange X x U) (i : ι)
    (hui : ofOver.pointsEquiv ((U i).toOver) (U i).point ∈
      closedPoints (Points (ofOver ((U i).toOver))))
    {Y : AlgebraicSpace S} (g : Y ⟶ ofOver ((U i).toOver)) :
    IsIsoOverOpen g (openInverseImageι (U i).hom (closedPointsComplementι X x hx)) ↔
      IsIsoOverOpen g (closedPointComplementι (ofOver ((U i).toOver)) hui) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
