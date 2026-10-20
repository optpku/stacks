module

public import ReasLib.RingTheory.Normal.Ring
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocalRingProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Birational
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.IsomorphismLocus

/-!
# Isomorphism loci of proper birational morphisms

A proper birational morphism of algebraic spaces into a Noetherian target, with
reduced source, is an isomorphism over every codimension-zero point, every
normal codimension-one point, and every normal point with finite fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A proper birational morphism from a reduced algebraic space to a Noetherian
algebraic space is an isomorphism over every codimension-zero point. -/
@[stacks 0BBQ]
theorem mem_isomorphismLocus_of_localRingDimAt_eq_zero
    {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    [IsDecent Y] [IsDecent X]
    [HasFiniteIrreducibleComponents Y] [HasFiniteIrreducibleComponents X]
    [IsNoetherian X] [IsReduced Y] (f : Y ⟶ X) [IsBirational f] [Proper f]
    {x : Points X} (hx : localRingDimAt x = 0) :
    x ∈ isomorphismLocus f :=
  sorry

/-- A proper birational morphism from a reduced algebraic space to a Noetherian
algebraic space is an isomorphism over every normal codimension-one point. -/
@[stacks 0BBQ]
theorem mem_isomorphismLocus_of_localRingDimAt_eq_one_of_normal
    {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    [IsDecent Y] [IsDecent X]
    [HasFiniteIrreducibleComponents Y] [HasFiniteIrreducibleComponents X]
    [IsNoetherian X] [IsReduced Y] (f : Y ⟶ X) [IsBirational f] [Proper f]
    {x : Points X} (hx : localRingDimAt x = 1)
    (hN : localRingHas (fun R ↦ IsNormalRing R) X x) :
    x ∈ isomorphismLocus f :=
  sorry

/-- A proper birational morphism from a reduced algebraic space to a Noetherian
algebraic space is an isomorphism over every point with finite set-theoretic
fibre and normal local ring. -/
@[stacks 0BBQ]
theorem mem_isomorphismLocus_of_finite_fiberOver_of_normal
    {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    [IsDecent Y] [IsDecent X]
    [HasFiniteIrreducibleComponents Y] [HasFiniteIrreducibleComponents X]
    [IsNoetherian X] [IsReduced Y] (f : Y ⟶ X) [IsBirational f] [Proper f]
    {x : Points X} (hfin : (fiberOver f x).Finite)
    (hN : localRingHas (fun R ↦ IsNormalRing R) X x) :
    x ∈ isomorphismLocus f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
