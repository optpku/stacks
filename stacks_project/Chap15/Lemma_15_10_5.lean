/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Jacobson.Localization
import StacksCheckRecall

/-!
# Lemma 15.10.5

@stack 0GED
-/

@[expose] public section

universe u

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A) (hI : I ≤ Ring.jacobson A)
variable (f : A) (hf : f ∈ I)

-- Lemma 15.10.5 (0GED): for a Noetherian Zariski pair `(A, I)` and `f ∈ I`, the
-- canonical away localization `A_f` is a Jacobson ring.
@[stacks 0GED]
#check
  (IsJacobsonRing.of_isLocalizationAway_of_mem_of_le_jacobson
      (S := Localization.Away f) I hI f hf :
    IsJacobsonRing (Localization.Away f))
