module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Integral.Dimension

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom.ProperBirational

/-- A proper birational morphism to a proper scheme of dimension at most one over a field
has source of dimension at most one. -/
theorem topologicalKrullDim_le_one
    (k : Type u) [Field k] {X X' : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p]
    (f : X' ⟶ X) (hdim : topologicalKrullDim X ≤ 1)
    [IsProper f] [IsBirational f] :
    topologicalKrullDim X' ≤ 1 := sorry

end AlgebraicGeometry.Scheme.Hom.ProperBirational
