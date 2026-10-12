/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Cohomology
public import ReasLib.Topology.Algebra.Group.FiniteGeneration

@[expose] public section

universe u

namespace CategoryTheory.Action.ModuleCat.DiscreteModuleCat

/-- The first cohomology module of a finite-dimensional discrete module over a topologically
finitely generated group is finite-dimensional. -/
theorem finiteDimensional_h1
    {k G : Type u} [Field k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteModuleCat k G) [FiniteDimensional k M.obj.V]
    (hG : TopologicalGroup.IsFinitelyGenerated G) :
    FiniteDimensional k (cohomologyObject k G 1 M) := sorry

/-- Finite generation of the group can be supplied through a `Fact` instance to infer the finite
dimensionality of first cohomology. -/
instance instFiniteDimensionalH1
    {k G : Type u} [Field k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteModuleCat k G) [FiniteDimensional k M.obj.V]
    [Fact (TopologicalGroup.IsFinitelyGenerated G)] :
    FiniteDimensional k (cohomologyObject k G 1 M) := sorry

end CategoryTheory.Action.ModuleCat.DiscreteModuleCat
