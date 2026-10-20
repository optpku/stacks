/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ResidueFieldTrdeg

/-!
# Dimension of group algebraic spaces over fields

A group algebraic space locally of finite type over a field has the same
dimension at every point. At a point of residue-field transcendence degree zero,
this dimension also equals the dimension of the local ring.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- The dimension of a group algebraic space locally of finite type over a field
equals its dimension at every point. -/
theorem dimension_eq_dimensionAt {S : Scheme.{u}} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ)))
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] (g : Points G.X.left) :
    dimension G.X.left = dimensionAt g := sorry

/-- At a point of residue-field transcendence degree zero over the base field,
the dimension of a locally finite type group algebraic space equals the
dimension of its local ring. -/
theorem dimension_eq_localRingDimAt_of_trdeg_eq_zero {S : Scheme.{u}}
    {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ)))
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] (g : Points G.X.left)
    (htrdeg : residueFieldTrdegAt G.X.hom g = 0) :
    dimension G.X.left = localRingDimAt g := sorry

/-- The dimension at a point of a group algebraic space locally of finite type
over a field is independent of the point. -/
theorem dimensionAt_eq {S : Scheme.{u}} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ)))
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] (g g' : Points G.X.left) :
    dimensionAt g = dimensionAt g' := sorry

/-- At a point of residue-field transcendence degree zero over the base field,
the dimension of a locally finite type group algebraic space equals the Krull
dimension of the étale local ring at every geometric point lying over it. -/
theorem dimension_eq_ringKrullDim_etaleLocalRing_of_trdeg_eq_zero
    {S : Scheme.{u}} {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ)))
    [AlgebraicSpace.LocallyOfFiniteType G.X.hom] (g : Points G.X.left)
    (gbar : GeometricPoint G.X.left) (hover : gbar.liesOver g)
    (htrdeg : residueFieldTrdegAt G.X.hom g = 0) :
    dimension G.X.left = ringKrullDim (etaleLocalRing G.X.left gbar) := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
