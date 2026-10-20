module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import Mathlib.Topology.JacobsonSpace

@[expose] public section

open AlgebraicGeometry CategoryTheory Set TopologicalSpace

universe u

namespace AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme

/-- An irreducible reduced closed subscheme of the projective plane is a closed
point, a positive-degree irreducible hypersurface, or the whole projective plane. -/
@[stacks 02A8]
theorem eq_closedPoint_or_hasHomogeneousEquation_or_isIso
    (k : Type u) [Field k] (Z : (ProjectiveSpace.scheme k 2).IdealSheafData)
    [IsReduced Z.subscheme] [IrreducibleSpace Z.subscheme] :
    (∃ x : ProjectiveSpace.scheme k 2,
        x ∈ closedPoints (ProjectiveSpace.scheme k 2) ∧
          (Z.support : Set (ProjectiveSpace.scheme k 2)) = {x}) ∨
      (∃ F : MvPolynomial (Fin 3) k,
        0 < F.totalDegree ∧ Irreducible F ∧ HasHomogeneousEquation 2 Z F) ∨
      IsIso Z.subschemeι :=
  sorry

end AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
