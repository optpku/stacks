/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.BrauerGroup.DegreeClasses
public import ReasLib.Algebra.GroupCohomology.Nonabelian
public import Mathlib.FieldTheory.Galois.IsGaloisGroup

@[expose] public section

universe u v

open scoped MatrixGroups

namespace CSA

/-- Isomorphism classes of central simple `K`-algebras of positive degree `d` are in bijection
with continuous non-abelian `H¹` of `Gal(Ksep / K)` with discrete coefficients `PGL(d, Ksep)`,
where `Ksep` is a separable algebraic closure of `K`. -/
theorem degreeAlgebraClasses_equiv_continuousNonabelianH1
    {K : Type u} [Field K] {Ksep : Type v} [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep] (d : ℕ) (hd : 0 < d) :
    Nonempty
      (degreeAlgebraClasses.{u, u} (K := K) d ≃
        GroupCohomology.continuousNonabelianH1 (G := Gal(Ksep / K)) (A := PGL(d, Ksep))) := sorry

end CSA

end
