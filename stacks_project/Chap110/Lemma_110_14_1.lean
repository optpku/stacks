/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Module.Int.PrimeDirectSum

/-!
# Nonsplit locally split sequences

A short exact sequence of modules which does not split globally, but splits Zariski
locally on a principal-open cover.
-/

@[expose] public section

universe u

open CategoryTheory

/- Lemma 110.14.1: there exists a ring `R` and a nonsplit sequence of `R`-modules
which becomes split Zariski locally. -/
@[stacks 0H7G] #check (Int.PrimeDirectSum.exists_nonsplit_zariskiLocallySplit :
    ∃ (R : Type u) (_ : CommRing R) (S : ShortComplex (ModuleCat.{u} R)),
      S.ShortExact ∧ ¬ Nonempty S.Splitting ∧
        ∃ s : Set R, Ideal.span s = ⊤ ∧
          ∀ f : s, Nonempty
            ((S.map (ModuleCat.localizedModuleFunctor (Submonoid.powers f.1))).Splitting))
