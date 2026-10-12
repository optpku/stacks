/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- For a separated scheme of finite type over a field, the cohomology module of
a coherent module in the degree of the topological Krull dimension is finite-dimensional
over the base field. -/
theorem topCohomology_finiteDimensional {k : Type u} [Field k]
    (X : SchemeOverField k) [Algebraic X] [IsSeparated X.hom]
    [HasExt (Sheaf (Opens.grothendieckTopology X.left.carrier) AddCommGrpCat.{u})]
    (F : X.left.Modules) [F.IsCoherent] (d : ℕ)
    (h_dimension : topologicalKrullDim X.left = (d : WithBot ℕ∞)) :
    FiniteDimensional k (Scheme.Hom.cohomology X.hom F d) := sorry

end AlgebraicGeometry.SchemeOverField

end
