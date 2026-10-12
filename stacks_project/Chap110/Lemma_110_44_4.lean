/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Frobenius.Subfield
public import ReasLib.RingTheory.Excellent

@[expose] public section

universe u

open IsLocalRing
open FieldExtension.Frobenius

namespace IsRegularLocalRing

/-- Lemma 110.44.4: a regular local ring `(A, m, κ)` of characteristic `p > 0` with
`[κ : κ ^ p] < ∞` is excellent if and only if the canonical map
`A → AdicCompletion (maximalIdeal A) A` is formally étale. -/
@[stacks 0G68]
theorem isExcellentRing_iff_algebraMap_formallyEtale
    {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] [CharP A p]
    [IsRegularLocalRing A] [CharP (ResidueField A) p]
    [FiniteDimensional (subfield p (ResidueField A)) (ResidueField A)] :
    IsExcellentRing.{u, u} A ↔
      Algebra.FormallyEtale A (AdicCompletion (maximalIdeal A) A) := sorry

end IsRegularLocalRing
