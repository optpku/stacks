/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OnField.Dimension
import StacksCheckRecall

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

/- Lemma 79.9.9 (1): in Situation 79.9.2, if `G.s` and `G.t` are locally of finite
type, then for every point `r` of `|G.R|` one has
`dimension G.R.left = dimensionAt r`. -/
@[stacks 06FD] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.dimension_eq_dimensionAt :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r : Points G.R.left),
    dimension G.R.left = dimensionAt r)

/- Lemma 79.9.9 (2): in Situation 79.9.2, if `G.s` and `G.t` are locally of finite
type, then for every point `r` of `|G.R|` the residue-field transcendence degree of
`r` over `Spec (.of k)` via `G.s` equals that via `G.t`. -/
@[stacks 06FD] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.residueFieldTrdegAt_source_eq_target :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r : Points G.R.left),
    residueFieldTrdegAt G.s.left r = residueFieldTrdegAt G.t.left r)

/- Lemma 79.9.9 (3): in Situation 79.9.2, if `G.s` and `G.t` are locally of finite
type and the residue-field transcendence degree of `r` over `Spec (.of k)` via
`G.s` is `0`, then `dimension G.R.left = localRingDimAt r`. -/
@[stacks 06FD] #check (AlgebraicGeometry.GroupoidAlgebraicSpace.dimension_eq_localRingDimAt_of_trdeg_eq_zero :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r : Points G.R.left) (htrdeg : residueFieldTrdegAt G.s.left r = 0),
    dimension G.R.left = localRingDimAt r)

/- In Situation 79.9.2, if `G.s` and `G.t` are locally of finite type, then the
dimension of `G.R` is independent of the chosen point of `|G.R|`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.dimensionAt_eq :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r r' : Points G.R.left),
    dimensionAt r = dimensionAt r')

/- Source-notation form of (3): if the residue-field transcendence degree of `r`
via `G.s` vanishes, then the dimension of `G.R` equals the Krull dimension of the
étale local ring at any geometric point over `r`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.dimension_eq_ringKrullDim_etaleLocalRing_of_trdeg_eq_zero :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r : Points G.R.left) (rbar : GeometricPoint G.R.left)
    (hover : rbar.liesOver r) (htrdeg : residueFieldTrdegAt G.s.left r = 0),
    dimension G.R.left = ringKrullDim (etaleLocalRing G.R.left rbar))

end AlgebraicGeometry.GroupoidAlgebraicSpace
