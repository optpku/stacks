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
public import stacks_project.Chap78.Definition_78_5_1_Group

/-!
# Dimension of groups over fields

In Situation 79.9.1, if a group algebraic space over `Spec (.of k)` is locally of
finite type, then it is equidimensional, and vanishing residue-field
transcendence degree identifies the global dimension with the dimension of the
local ring.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- Lemma 79.9.10 (1): in Situation 79.9.1, if `G` is locally of finite type,
then for every point `g` of `|G|` one has
`dimension G.X.left = dimensionAt g`. -/
@[stacks 06FE]
theorem dimension_eq_dimensionAt {S : Scheme.{u}} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ)))
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] (g : Points G.X.left) :
    dimension G.X.left = dimensionAt g := sorry

/-- Lemma 79.9.10 (2): in Situation 79.9.1, if `G` is locally of finite type
and the residue-field transcendence degree of `g` over `k` is `0`, then
`dimension G.X.left = localRingDimAt g`. -/
@[stacks 06FE]
theorem dimension_eq_localRingDimAt_of_trdeg_eq_zero {S : Scheme.{u}}
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ)))
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] (g : Points G.X.left)
    (htrdeg : residueFieldTrdegAt G.X.hom g = 0) :
    dimension G.X.left = localRingDimAt g := sorry

/-- In Situation 79.9.1, if `G` is locally of finite type, then the dimension of
`G` is independent of the chosen point of `|G|`. -/
theorem dimensionAt_eq {S : Scheme.{u}} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ)))
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] (g g' : Points G.X.left) :
    dimensionAt g = dimensionAt g' := sorry

/-- Source-notation form of (2): if the residue-field transcendence degree of `g`
over `k` vanishes, then the dimension of `G` equals the Krull dimension of the
étale local ring at any geometric point over `g`. -/
theorem dimension_eq_ringKrullDim_etaleLocalRing_of_trdeg_eq_zero
    {S : Scheme.{u}} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ)))
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] (g : Points G.X.left)
    (gbar : GeometricPoint G.X.left) (hover : gbar.liesOver g)
    (htrdeg : residueFieldTrdegAt G.X.hom g = 0) :
    dimension G.X.left = ringKrullDim (etaleLocalRing G.X.left gbar) := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
