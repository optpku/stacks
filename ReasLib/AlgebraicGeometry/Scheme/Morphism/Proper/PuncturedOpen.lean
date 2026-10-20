module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Opens

/-- The complement of a closed point in a positive-dimensional irreducible scheme, separated
over a field, is not proper over that field. -/
theorem not_isProper_comp_of_compl_closedPoint
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [IrreducibleSpace X]
    (hdim : (0 : WithBot ℕ∞) < topologicalKrullDim X)
    (x : X) (hx : x ∈ closedPoints X)
    (U : X.Opens) (hU : (U : Set X) = ({x} : Set X)ᶜ) :
    ¬ IsProper (U.ι ≫ f) := sorry

end AlgebraicGeometry.Scheme.Opens
