/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cochain Differential Graded Algebras Concentrated in Degree Zero

This is the literal formal counterpart of regarding an ordinary algebra as a cochain
differential graded algebra: every homogeneous component away from degree zero is a zero object.
-/

@[expose] public section

noncomputable section

open CategoryTheory.Limits

universe u

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

/-- A cochain differential graded algebra is concentrated in degree zero when every component
of nonzero degree is a zero module. -/
@[stacks 09SA "differential graded algebra concentrated in degree zero"]
def IsConcentratedInDegreeZero (A : CochainDGAlgebra R) : Prop :=
  ∀ n : ℤ, n ≠ 0 → IsZero (A.X n)

/-- The defining componentwise characterization of concentration in degree zero. -/
theorem isConcentratedInDegreeZero_iff (A : CochainDGAlgebra R) :
    A.IsConcentratedInDegreeZero ↔ ∀ n : ℤ, n ≠ 0 → IsZero (A.X n) := sorry

/-- Every nonzero-degree component of an algebra concentrated in degree zero is zero. -/
theorem IsConcentratedInDegreeZero.isZero_X {A : CochainDGAlgebra R}
    (hA : A.IsConcentratedInDegreeZero) (n : ℤ) (hn : n ≠ 0) :
    IsZero (A.X n) := sorry

/-- Every differential of a cochain differential graded algebra concentrated in degree zero is
zero. -/
theorem IsConcentratedInDegreeZero.d_eq_zero {A : CochainDGAlgebra R}
    (hA : A.IsConcentratedInDegreeZero) (n : ℤ) :
    A.d n = 0 := sorry

/-- Homology away from degree zero vanishes for an algebra concentrated in degree zero. -/
theorem IsConcentratedInDegreeZero.isZero_homology {A : CochainDGAlgebra R}
    (hA : A.IsConcentratedInDegreeZero) (n : ℤ) (hn : n ≠ 0) :
    IsZero (A.homology n) := sorry

/-- The canonical identification `H^0(A) ≅ A^0` for a cochain differential graded algebra
concentrated in degree zero. -/
noncomputable def IsConcentratedInDegreeZero.homologyZeroIso
    {A : CochainDGAlgebra R} (hA : A.IsConcentratedInDegreeZero) :
    A.homology 0 ≅ A.X 0 :=
  (A.toCochainComplex.isoHomologyπ (0 - 1) 0 (CochainComplex.prev ℤ 0)
    (hA.d_eq_zero (0 - 1))).symm ≪≫
      A.toCochainComplex.iCyclesIso 0 (0 + 1) (CochainComplex.next ℤ 0)
        (hA.d_eq_zero 0)

end CochainDGAlgebra
