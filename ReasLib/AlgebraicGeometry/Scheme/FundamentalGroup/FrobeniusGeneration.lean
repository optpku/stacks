module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Algebra.Group.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Frobenius

/-!
# Topological generation of π₁ by finitely many Frobenius classes

For a smooth geometrically irreducible projective curve over a finite field,
finitely many closed points have geometric Frobenius conjugacy classes that
topologically generate the étale fundamental group.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)

/-- The set of all geometric Frobenius elements in
`Aut (GeometricPoint.finiteFiber xbar)` associated to a closed point, obtained as
the path-transports of local geometric Frobenius along fibre isomorphisms. -/
def etaleGeometricFrobeniusSet [Finite k] [ConnectedSpace X.left]
    [LocallyOfFiniteType X.hom] (xbar : GeometricPoint X.left)
    (v : closedPoints X.left) :
    Set (Aut (GeometricPoint.finiteFiber xbar)) :=
  Set.range (etaleGeometricFrobenius X xbar v)

/-- Unfolding of `etaleGeometricFrobeniusSet` as the range of
`etaleGeometricFrobenius`. -/
theorem etaleGeometricFrobeniusSet_spec [Finite k] [ConnectedSpace X.left]
    [LocallyOfFiniteType X.hom] (xbar : GeometricPoint X.left)
    (v : closedPoints X.left) :
    etaleGeometricFrobeniusSet X xbar v =
      Set.range (etaleGeometricFrobenius X xbar v) := rfl

/-- Each path-transport of local geometric Frobenius at a closed point lies in
`etaleGeometricFrobeniusSet`. -/
theorem etaleGeometricFrobenius_mem_set [Finite k] [ConnectedSpace X.left]
    [LocallyOfFiniteType X.hom] (xbar : GeometricPoint X.left)
    (v : closedPoints X.left)
    (ι : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅
      GeometricPoint.finiteFiber xbar) :
    etaleGeometricFrobenius X xbar v ι ∈ etaleGeometricFrobeniusSet X xbar v :=
  ⟨ι, rfl⟩

/-- Let `k` be a finite field and let `X` be a smooth,
geometrically irreducible projective curve over `k`. For any geometric point
`xbar` of `X`, there exists a finite set of closed points of `X` such that the
set of all geometric Frobenius elements in `etaleFundamentalGroup X.left xbar`
corresponding to these points topologically generates `π₁(X, xbar)`. -/
@[stacks 03W5]
theorem exists_finset_etaleGeometricFrobenius_topologicallyGenerate
    [Finite k] [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] [ConnectedSpace X.left]
    (xbar : GeometricPoint X.left) :
    ∃ S : Finset (closedPoints X.left),
      (Subgroup.closure
          (⋃ v ∈ S, etaleGeometricFrobeniusSet X xbar v)).topologicalClosure = ⊤ :=
  sorry

/-- For a smooth geometrically irreducible projective curve over a finite field,
there exists a finite set of closed points such that for every choice of one
geometric Frobenius element at each point, the topological closure of the
normal closure of those elements is all of `π₁(X, xbar)`. -/
theorem exists_finset_etaleGeometricFrobenius_normalClosure
    [Finite k] [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] [ConnectedSpace X.left]
    (xbar : GeometricPoint X.left) :
    ∃ S : Finset (closedPoints X.left),
      ∀ F : S → Aut (GeometricPoint.finiteFiber xbar),
        (∀ v : S, F v ∈ etaleGeometricFrobeniusSet X xbar v.1) →
          (Subgroup.normalClosure (Set.range F)).topologicalClosure = ⊤ :=
  sorry

/-- For a connected scheme locally of finite type over a finite field and a
fixed finite set of closed points, topological generation by all
associated geometric Frobenius elements is equivalent to every choice of one
geometric Frobenius per point having topological normal closure equal to the
whole étale fundamental group. -/
theorem etaleGeometricFrobenius_topologicallyGenerate_iff_normalClosure
    [Finite k] [ConnectedSpace X.left] [LocallyOfFiniteType X.hom]
    (xbar : GeometricPoint X.left) (S : Finset (closedPoints X.left)) :
    (Subgroup.closure
        (⋃ v ∈ S, etaleGeometricFrobeniusSet X xbar v)).topologicalClosure = ⊤ ↔
      ∀ F : S → Aut (GeometricPoint.finiteFiber xbar),
        (∀ v : S, F v ∈ etaleGeometricFrobeniusSet X xbar v.1) →
          (Subgroup.normalClosure (Set.range F)).topologicalClosure = ⊤ :=
  sorry

end AlgebraicGeometry.SchemeOverField
