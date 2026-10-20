/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Sequence.Regularity.Counterexample
import StacksCheckRecall

@[expose] public section

universe u

open IsLocalRing

namespace RingTheory.Sequence

/- Lemma 110.15.2: there exists a local homomorphism of local rings `algebraMap A B` and a
regular sequence `x`, `y` in `maximalIdeal B` such that `B ⧸ Ideal.ofList [x, y]` is flat over
`A`, but the images of `x`, `y` in `B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)` form
neither a regular sequence nor a Koszul-regular sequence. -/
@[stacks 0641] #check (RingTheory.Sequence.exists_isLocalHom_isRegular_flatQuotient_not_isKoszulRegular :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : IsLocalRing A) (_ : IsLocalRing B)
      (_ : Algebra A B) (_ : IsLocalHom (algebraMap A B)) (x y : B),
      let I := Ideal.map (algebraMap A B) (maximalIdeal A)
      let xbar := Ideal.Quotient.mk I x
      let ybar := Ideal.Quotient.mk I y
      IsRegular B [x, y] ∧
        Ideal.ofList [x, y] ≤ maximalIdeal B ∧
        Module.Flat A (B ⧸ Ideal.ofList [x, y]) ∧
        ¬ IsRegular (B ⧸ I) [xbar, ybar] ∧
        ¬ IsKoszulRegularSequence (Fin.cons xbar (Fin.cons ybar Fin.elim0)))

end RingTheory.Sequence
