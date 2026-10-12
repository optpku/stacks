/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.LocallyFree.Descent
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v w

/- Remark 35.7.8 (1): local freeness of modules does not descend along arbitrary
faithfully flat ring maps, even for projective modules that are countable direct sums
of finite locally free modules of rank one and become free after base change. -/
@[stacks 05VF] #check (Module.LocallyFree.not_fpqcLocal :
    ¬ ∀ (A : Type u) [CommRing A] (B : Type v) [CommRing B] [Algebra A B]
        (M : Type w) [AddCommGroup M] [Module A M] (L : ℕ → Submodule A M),
      Module.Projective A M →
      iSupIndep L →
      iSup L = ⊤ →
      (∀ n, Module.FiniteLocallyFreeOfRank A (L n) 1) →
      (algebraMap A B).FaithfullyFlat →
      Module.Free B (B ⊗[A] M) →
      Module.LocallyFree A M)

-- Whether the analogous implication holds for arbitrary faithfully flat maps of finite
-- presentation remains open; the next theorem records the known Noetherian case.

/- Remark 35.7.8 (2): over a Noetherian ring, an `A`-module that becomes free after a
faithfully flat base change of finite presentation is locally free. -/
@[stacks 05VF] #check (Module.LocallyFree.of_fppfFreeBaseChange :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
      {M : Type w} [AddCommGroup M] [Module A M] [IsNoetherianRing A],
      (algebraMap A B).FaithfullyFlat →
      (algebraMap A B).FinitePresentation →
      Module.Free B (B ⊗[A] M) →
      Module.LocallyFree A M)
