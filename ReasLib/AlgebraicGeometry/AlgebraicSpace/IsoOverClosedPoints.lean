/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Pi.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedPoints.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedPoints.Complement

/-! # Morphisms that are isomorphisms away from a finite family of closed points -/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

variable {ι : Type v} [Finite ι] {S : Scheme.{u}}

/-- The category of morphisms `Y ⟶ X` that are isomorphisms over `X \ {x i}`. -/
abbrev IsoOverClosedPoints (X : AlgebraicSpace S) (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) :=
  IsoOverOpen (closedPointsComplementι X x hx)

/-- The shrinking condition that each neighbourhood `U i` meets the family `{x j}`
only at the selected point `u i`. -/
def supportedOnRange (X : AlgebraicSpace S) (x : ι → Points X)
    (U : ∀ i, EtaleNeighborhood X (x i)) : Prop :=
  ∀ i, Points.mapOfOver (U i).hom ⁻¹' Set.range x = {(U i).point}

namespace IsoOverClosedPoints

/-- Base change along a family of étale neighbourhoods takes morphisms that are
isomorphisms outside the finite range to morphisms that are isomorphisms over its
inverse images. -/
def baseChangeFamily (X : AlgebraicSpace S) (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) :
    IsoOverClosedPoints X x hx ⥤
      ∀ i, IsoOverOpen (openInverseImageι (U i).hom (closedPointsComplementι X x hx)) :=
  Functor.pi' fun i ↦
    IsoOverOpen.baseChange (U i).hom (closedPointsComplementι X x hx)

/-- Projecting `baseChangeFamily` at an index recovers base change along that
neighbourhood. -/
def baseChangeFamily_eval (X : AlgebraicSpace S) (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (i : ι) :
    baseChangeFamily X x hx U ⋙ Pi.eval _ i ≅
      IsoOverOpen.baseChange (U i).hom (closedPointsComplementι X x hx) :=
  Functor.pi'CompEval
    (fun j ↦ IsoOverOpen.baseChange (U j).hom (closedPointsComplementι X x hx)) i

end IsoOverClosedPoints

/-- Under the shrinking condition, the selected point of each neighbourhood is closed
in the algebraic space associated to that neighbourhood. -/
theorem isClosed_neighborhoodPoint (X : AlgebraicSpace S)
    (x : ι → Points X) (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (hU : supportedOnRange X x U) (i : ι) :
    ofOver.pointsEquiv ((U i).toOver) (U i).point ∈
      closedPoints (Points (ofOver ((U i).toOver))) :=
  sorry

/-- Under the shrinking condition, being an isomorphism over the inverse image of
`X \ {x i}` is equivalent to being an isomorphism over `U i \ {u i}`. -/
theorem isIsoOverOpen_openInverseImage_iff_closedPointComplement
    (X : AlgebraicSpace S) (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (U : ∀ i, EtaleNeighborhood X (x i)) (hU : supportedOnRange X x U) (i : ι)
    (hui : ofOver.pointsEquiv ((U i).toOver) (U i).point ∈
      closedPoints (Points (ofOver ((U i).toOver))))
    {Y : AlgebraicSpace S} (g : Y ⟶ ofOver ((U i).toOver)) :
    IsIsoOverOpen g (openInverseImageι (U i).hom (closedPointsComplementι X x hx)) ↔
      IsIsoOverOpen g (closedPointComplementι (ofOver ((U i).toOver)) hui) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
