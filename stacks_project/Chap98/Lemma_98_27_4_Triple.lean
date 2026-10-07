module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap70.Lemma_70_19_1_IsoOverOpen
public import stacks_project.Chap80.Definition_80_3_1_RelativelyRepresentable
public import stacks_project.Chap98.Situation_98_27_1_Contraction

/-!
# Compatible contraction triples

In a contraction situation, a triple on a locally Noetherian scheme `V` over `S`
consists of a closed subset `Z ⊂ |V|`, a morphism `u'` from the open complement
of `Z` into `U'`, and an adic morphism `hatx` from the completion of `V` along
`Z` into `W`, together with the compatibility witness of a proper isomorphism
over `V \ Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- Data witnessing that `u'` and `hatx` are compatible: a proper morphism
`toV : V' ⟶ ofOver V` which is an isomorphism over the open complement of `Z`,
a cartesian square of `hatx'` against `σ.g` and `hatx`, and a morphism
`x' : V' ⟶ σ.X'` restricting to `u'` and `hatx`. -/
structure CompatibilityWitness (σ : ContractionSituation S) (V : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian V.left]
    (Z : Closeds (Points (ofOver V)))
    (u' : openComplementAlong (ofOver V) Z ⟶ σ.openComplement)
    (hatx : completionAlong (ofOver V) Z ⟶ σ.W) where
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
  /-- `V' ⟶ V` is proper. -/
  proper_toV : Proper toV
  /-- `V' ⟶ V` is an isomorphism over `V \ Z`. -/
  isoOverOpen_toV : IsIsoOverOpen toV (AlgebraicGeometry.AlgebraicSpace.openComplementι (ofOver V) Z)
  /-- The open complement of `Z` includes into `V` through `V'`. -/
  openToV'_comp_toV : openToV' ≫ toV = AlgebraicGeometry.AlgebraicSpace.openComplementι (ofOver V) Z
  /-- The square of `hatx'` against `σ.g` and `hatx` is cartesian. -/
  isPullback : IsPullback hatx' (completionAlong.map toV Z) σ.g hatx
  /-- `x'` restricts to `u'` on `V \ Z`. -/
  restricts_u' : openToV' ≫ x' = u' ≫ σ.openComplementι
  /-- `x'` restricts to `hatx'` on the completion of `V'` along `Z`. -/
  restricts_hatx :
    hatx' ≫ completionAlong.ι σ.X' σ.T' =
      completionAlong.ι V' (Z.preimage (Points.continuous_map toV)) ≫ x'

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
    (x' : V' ⟶ σ.X') : CompatibilityWitness σ V Z u' hatx where
  V' := V'
  toV := toV
  openToV' := openToV'
  hatx' := hatx'
  x' := x'
  proper_toV := sorry
  isoOverOpen_toV := sorry
  openToV'_comp_toV := sorry
  isPullback := sorry
  restricts_u' := sorry
  restricts_hatx := sorry

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
  sorry

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
    (hatx : completionAlong (ofOver V) Z ⟶ σ.W) : Triple σ V where
  Z := Z
  u' := u'
  hatx := hatx
  isAdic := sorry
  isCompatible := sorry

/-- The first component of a triple is a closed subset of the points of `V`. -/
theorem Triple.spec_Z {σ : ContractionSituation S} {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (ξ : Triple σ V) :
    IsClosed (ξ.Z : Set (Points (ofOver V))) :=
  sorry

/-- The second component of a triple is a morphism from `V \ Z` into `U'`. -/
theorem Triple.spec_u' {σ : ContractionSituation S} {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (ξ : Triple σ V) :
    ξ.u' ≫ σ.openComplementι =
      ξ.u' ≫ ContractionSituation.openComplementι σ :=
  sorry

/-- The third component of a triple is an adic morphism of formal algebraic
spaces. -/
theorem Triple.spec_adic {σ : ContractionSituation S} {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (ξ : Triple σ V) :
    representableByAlgebraicSpaces ξ.hatx :=
  sorry

/-- The components of a triple are compatible. -/
theorem Triple.spec_compatible {σ : ContractionSituation S} {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (ξ : Triple σ V) :
    IsCompatible σ V ξ.Z ξ.u' ξ.hatx :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
