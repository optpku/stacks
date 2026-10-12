/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_33_3_ResidueFieldTrdeg
public import stacks_project.Chap79.Situation_79_9_2_OnField

/-!
# Dimension of groupoids on fields

In Situation 79.9.2, if the source and target maps are locally of finite type,
then the arrow space is equidimensional, the two residue-field transcendence
degrees of a point agree, and vanishing transcendence degree identifies the
global dimension with the dimension of the local ring.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 79.9.9 (1): in Situation 79.9.2, if `G.s` and `G.t` are locally of finite
type, then for every point `r` of `|G.R|` one has
`dimension G.R.left = dimensionAt r`. -/
@[stacks 06FD]
theorem dimension_eq_dimensionAt {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r : Points G.R.left) :
    dimension G.R.left = dimensionAt r := sorry

/-- Lemma 79.9.9 (2): in Situation 79.9.2, if `G.s` and `G.t` are locally of finite
type, then for every point `r` of `|G.R|` the residue-field transcendence degree of
`r` over `Spec (.of k)` via `G.s` equals that via `G.t`. -/
@[stacks 06FD]
theorem residueFieldTrdegAt_source_eq_target {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r : Points G.R.left) :
    residueFieldTrdegAt G.s.left r = residueFieldTrdegAt G.t.left r := sorry

/-- Lemma 79.9.9 (3): in Situation 79.9.2, if `G.s` and `G.t` are locally of finite
type and the residue-field transcendence degree of `r` over `Spec (.of k)` via
`G.s` is `0`, then `dimension G.R.left = localRingDimAt r`. -/
@[stacks 06FD]
theorem dimension_eq_localRingDimAt_of_trdeg_eq_zero
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r : Points G.R.left) (htrdeg : residueFieldTrdegAt G.s.left r = 0) :
    dimension G.R.left = localRingDimAt r := sorry

/-- In Situation 79.9.2, if `G.s` and `G.t` are locally of finite type, then the
dimension of `G.R` is independent of the chosen point of `|G.R|`. -/
theorem dimensionAt_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r r' : Points G.R.left) :
    dimensionAt r = dimensionAt r' := sorry

/-- Source-notation form of (3): if the residue-field transcendence degree of `r`
via `G.s` vanishes, then the dimension of `G.R` equals the Krull dimension of the
étale local ring at any geometric point over `r`. -/
theorem dimension_eq_ringKrullDim_etaleLocalRing_of_trdeg_eq_zero
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r : Points G.R.left) (rbar : GeometricPoint G.R.left)
    (hover : rbar.liesOver r) (htrdeg : residueFieldTrdegAt G.s.left r = 0) :
    dimension G.R.left = ringKrullDim (etaleLocalRing G.R.left rbar) := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
