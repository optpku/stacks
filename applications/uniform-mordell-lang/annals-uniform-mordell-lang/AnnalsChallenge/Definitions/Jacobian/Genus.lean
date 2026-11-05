/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import JacobianFoundations.Genus

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.JacobianChallenge

/-- The genus is `dim_k H¹(C, O_C)`, supplied by the independent foundations package. -/
noncomputable def genus {k : Type u} [Field k]
    (C : Over (Spec (.of k))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom] : ℕ :=
  CurveJacobian.genus C

end AlgebraicGeometry.JacobianChallenge
