/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OnField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Stabilizer
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ResidueFieldTrdeg

/-!
# Dimension of groupoids on fields and their stabilizers

For a groupoid on a field with locally finite type source and target maps,
the arrow space is equidimensional and has the same dimension as its stabilizer.
The source and target residue-field transcendence degrees agree at every point;
when they vanish, the global dimension equals the dimension of the étale local ring.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- For a groupoid on a field whose source and target maps are locally of finite
type, the dimension of the arrow space equals its dimension at every point. -/
theorem dimension_eq_dimensionAt {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r : Points G.R.left) :
    dimension G.R.left = dimensionAt r := sorry

/-- For a groupoid on a field whose source and target maps are locally of finite
type, the residue-field transcendence degrees via the source and target agree
at every point of the arrow space. -/
theorem residueFieldTrdegAt_source_eq_target {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r : Points G.R.left) :
    residueFieldTrdegAt G.s.left r = residueFieldTrdegAt G.t.left r := sorry

/-- For a groupoid on a field whose source and target maps are locally of finite
type, vanishing source residue-field transcendence degree at a point identifies
the dimension of the arrow space with the local-ring dimension at that point. -/
theorem dimension_eq_localRingDimAt_of_trdeg_eq_zero
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r : Points G.R.left) (htrdeg : residueFieldTrdegAt G.s.left r = 0) :
    dimension G.R.left = localRingDimAt r := sorry

/-- For a groupoid on a field whose source and target maps are locally of finite
type, the dimension of the arrow space at a point is independent of the point. -/
theorem dimensionAt_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r r' : Points G.R.left) :
    dimensionAt r = dimensionAt r' := sorry

/-- For a groupoid on a field whose source and target maps are locally of finite
type, vanishing source residue-field transcendence degree at a point identifies
the dimension of the arrow space with the Krull dimension of the étale local
ring at every geometric point over that point. -/
theorem dimension_eq_ringKrullDim_etaleLocalRing_of_trdeg_eq_zero
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r : Points G.R.left) (rbar : GeometricPoint G.R.left)
    (hover : rbar.liesOver r) (htrdeg : residueFieldTrdegAt G.s.left r = 0) :
    dimension G.R.left = ringKrullDim (etaleLocalRing G.R.left rbar) := sorry

/-- For a groupoid on a field whose source and target maps are locally of finite
type, the dimension of the arrow space equals the dimension of the stabilizer
group algebraic space defined by the diagonal pullback of the target-source map. -/
theorem dimension_eq_stabilizer {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left] :
    dimension G.R.left = dimension G.stabilizer.X.left.left := sorry

/-- For a groupoid on a field whose source and target maps are locally of finite
type, the dimension at every point of the arrow space equals the dimension of
the stabilizer group algebraic space. -/
theorem dimensionAt_eq_dimension_stabilizer {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
    [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.LocallyOfFiniteType G.t.left]
    (r : Points G.R.left) :
    dimensionAt r = dimension G.stabilizer.X.left.left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
