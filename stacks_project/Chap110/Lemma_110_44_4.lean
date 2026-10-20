/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Completion.Excellent
import StacksCheckRecall

@[expose] public section

universe u

open IsLocalRing
open FieldExtension.Frobenius

/- Lemma 110.44.4: a regular local ring `(A, m, κ)` of characteristic `p > 0` with
`[κ : κ ^ p] < ∞` is excellent if and only if the canonical map
`A → AdicCompletion (maximalIdeal A) A` is formally étale. -/
@[stacks 0G68] #check (IsRegularLocalRing.isExcellentRing_iff_algebraMap_formallyEtale :
    ∀ {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] [CharP A p]
    [IsRegularLocalRing A] [CharP (ResidueField A) p]
    [FiniteDimensional (subfield p (ResidueField A)) (ResidueField A)],
    IsExcellentRing.{u, u} A ↔
      Algebra.FormallyEtale A (AdicCompletion (maximalIdeal A) A))
