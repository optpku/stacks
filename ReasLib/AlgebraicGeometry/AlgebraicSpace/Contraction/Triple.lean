/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- Objects and morphisms interpolating a compatibility diagram. -/
structure CompatibilityData (σ : ContractionSituation S) (V : Over S)
    (Z : Closeds (Points (ofOver V))) where
  /-- The algebraic space `V'` supplying the dilatation of `V` along `Z`. -/
  V' : AlgebraicSpace S
  /-- The structure morphism `V' ⟶ V`. -/
  toV : V' ⟶ ofOver V
  /-- The open complement of `Z` as an open of `V'`. -/
  openToV' : openComplementAlong (ofOver V) Z ⟶ V'
  /-- The morphism `hatx' : V'_{/Z} ⟶ X'_{/T'}` filling the cartesian square. -/
  hatx' : completionAlong V' (Z.preimage (Points.continuous_map toV)) ⟶ σ.completion
  /-- The morphism `x' : V' ⟶ X'` restricting to `u'` and `hatx`. -/
  x' : V' ⟶ σ.X'

/-- Properness, the cartesian square, and the two restrictions of fixed
interpolating data. -/
structure CompatibilityData.Properties {σ : ContractionSituation S} {V : Over S}
    {Z : Closeds (Points (ofOver V))}
    (D : CompatibilityData σ V Z)
    (u' : openComplementAlong (ofOver V) Z ⟶ σ.openComplement)
    (hatx : completionAlong (ofOver V) Z ⟶ σ.W) : Prop where
  /-- `D.V' ⟶ V` is proper. -/
  proper_toV : Proper D.toV
  /-- `D.V' ⟶ V` is an isomorphism over `V \ Z`. -/
  isoOverOpen_toV : IsIsoOverOpen D.toV (AlgebraicGeometry.AlgebraicSpace.openComplementι (ofOver V) Z)
  /-- The open complement of `Z` includes into `V` through `D.V'`. -/
  openToV'_comp_toV : D.openToV' ≫ D.toV = AlgebraicGeometry.AlgebraicSpace.openComplementι (ofOver V) Z
  /-- The square of `D.hatx'` against `σ.g` and `hatx` is cartesian. -/
  isPullback : IsPullback D.hatx' (completionAlong.map D.toV Z) σ.g hatx
  /-- `D.x'` restricts to `u'` on `V \ Z`. -/
  restricts_u' : D.openToV' ≫ D.x' = u' ≫ σ.openComplementι
  /-- `D.x'` restricts to `D.hatx'` on the completion of `D.V'` along `Z`. -/
  restricts_hatx :
    D.hatx' ≫ completionAlong.ι σ.X' σ.T' =
      completionAlong.ι D.V' (Z.preimage (Points.continuous_map D.toV)) ≫ D.x'

/-- Compatibility consists of interpolating data satisfying the geometric
and commutativity conditions, with the original inherited projections. -/
structure CompatibilityWitness (σ : ContractionSituation S) (V : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian V.left]
    (Z : Closeds (Points (ofOver V)))
    (u' : openComplementAlong (ofOver V) Z ⟶ σ.openComplement)
    (hatx : completionAlong (ofOver V) Z ⟶ σ.W)
    extends CompatibilityData σ V Z,
      CompatibilityData.Properties toCompatibilityData u' hatx

/-- Package a proper isomorphism over `V \ Z`, a cartesian filling `hatx'`, and a
morphism `x' : V' ⟶ X'` restricting to `u'` and `hatx`. -/
def CompatibilityWitness.of {σ : ContractionSituation S} {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left]
    {Z : Closeds (Points (ofOver V))}
    {u' : openComplementAlong (ofOver V) Z ⟶ σ.openComplement}
    {hatx : completionAlong (ofOver V) Z ⟶ σ.W}
    (V' : AlgebraicSpace S) (toV : V' ⟶ ofOver V)
    (openToV' : openComplementAlong (ofOver V) Z ⟶ V')
    (hatx' : completionAlong V' (Z.preimage (Points.continuous_map toV)) ⟶ σ.completion)
    (x' : V' ⟶ σ.X')
    (proper_toV : Proper toV)
    (isoOverOpen_toV : IsIsoOverOpen toV (AlgebraicSpace.openComplementι (ofOver V) Z))
    (openToV'_comp_toV : openToV' ≫ toV = AlgebraicSpace.openComplementι (ofOver V) Z)
    (isPullback : IsPullback hatx' (completionAlong.map toV Z) σ.g hatx)
    (restricts_u' : openToV' ≫ x' = u' ≫ σ.openComplementι)
    (restricts_hatx : hatx' ≫ completionAlong.ι σ.X' σ.T' =
      completionAlong.ι V' (Z.preimage (Points.continuous_map toV)) ≫ x') :
    CompatibilityWitness σ V Z u' hatx where
  V' := V'
  toV := toV
  openToV' := openToV'
  hatx' := hatx'
  x' := x'
  proper_toV := proper_toV
  isoOverOpen_toV := isoOverOpen_toV
  openToV'_comp_toV := openToV'_comp_toV
  isPullback := isPullback
  restricts_u' := restricts_u'
  restricts_hatx := restricts_hatx

/-- Compatibility of `u'` and `hatx` is witnessed by some proper isomorphism over
`V \ Z` together with cartesian `hatx'` and a restriction `x'`. -/
def IsCompatible (σ : ContractionSituation S) (V : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian V.left]
    (Z : Closeds (Points (ofOver V)))
    (u' : openComplementAlong (ofOver V) Z ⟶ σ.openComplement)
    (hatx : completionAlong (ofOver V) Z ⟶ σ.W) : Prop :=
  Nonempty (CompatibilityWitness σ V Z u' hatx)

/-- `IsCompatible` is the existence of a `CompatibilityWitness`. -/
theorem IsCompatible.iff {σ : ContractionSituation S} {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left]
    (Z : Closeds (Points (ofOver V)))
    (u' : openComplementAlong (ofOver V) Z ⟶ σ.openComplement)
    (hatx : completionAlong (ofOver V) Z ⟶ σ.W) :
    IsCompatible σ V Z u' hatx ↔ Nonempty (CompatibilityWitness σ V Z u' hatx) :=
  Iff.rfl

/-- A triple `(Z, u', hatx)` on a locally Noetherian scheme `V` over `S`: a closed
subset of `|V|`, a morphism from the open complement into `U'`, and an adic
morphism of formal algebraic spaces from the completion along `Z` into `W`,
satisfying compatibility. -/
structure Triple (σ : ContractionSituation S) (V : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian V.left] where
  /-- The closed subset `Z ⊂ |V|`. -/
  Z : Closeds (Points (ofOver V))
  /-- The morphism `u' : V \ Z ⟶ U'` over `S`. -/
  u' : openComplementAlong (ofOver V) Z ⟶ σ.openComplement
  /-- The morphism `hatx : V_{/Z} ⟶ W` of formal algebraic spaces over `S`. -/
  hatx : completionAlong (ofOver V) Z ⟶ σ.W
  /-- `hatx` is an adic morphism, i.e. representable by algebraic spaces. -/
  isAdic : representableByAlgebraicSpaces hatx
  /-- `u'` and `hatx` are compatible. -/
  isCompatible : IsCompatible σ V Z u' hatx

/-- Assemble a triple from a closed subset, an open morphism into `U'`, and a
morphism of completions into `W`. -/
def Triple.of {σ : ContractionSituation S} {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left]
    (Z : Closeds (Points (ofOver V)))
    (u' : openComplementAlong (ofOver V) Z ⟶ σ.openComplement)
    (hatx : completionAlong (ofOver V) Z ⟶ σ.W)
    (isAdic : representableByAlgebraicSpaces hatx)
    (isCompatible : IsCompatible σ V Z u' hatx) : Triple σ V where
  Z := Z
  u' := u'
  hatx := hatx
  isAdic := isAdic
  isCompatible := isCompatible

/-- The first component of a triple is a closed subset of the points of `V`. -/
theorem Triple.spec_Z {σ : ContractionSituation S} {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (ξ : Triple σ V) :
    IsClosed (ξ.Z : Set (Points (ofOver V))) :=
  ξ.Z.isClosed

/-- The third component of a triple is an adic morphism of formal algebraic
spaces. -/
theorem Triple.spec_adic {σ : ContractionSituation S} {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (ξ : Triple σ V) :
    representableByAlgebraicSpaces ξ.hatx :=
  ξ.isAdic

/-- The components of a triple are compatible. -/
theorem Triple.spec_compatible {σ : ContractionSituation S} {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (ξ : Triple σ V) :
    IsCompatible σ V ξ.Z ξ.u' ξ.hatx :=
  ξ.isCompatible

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
