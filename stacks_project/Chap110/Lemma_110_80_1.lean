module

import StacksCheckRecall
public import ReasLib.Algebra.Module.Descent.NonFPQC

@[expose] public section

universe u

/- Lemma 110.80.1: there exists a ring `A` and an infinite family of flat ring maps
`algebraMap A (A_ i)` such that every `A`-module `M` is the equalizer of
`∏ i, M ⊗[A] A_ i ⇉ ∏ i j, M ⊗[A] (A_ i ⊗[A] A_ j)`, but no finite subfamily has the
same property for every module. -/
@[stacks 0EUF] #check (Algebra.exists_infinite_flat_piTensorEqualizer_not_finite :
    ∃ (A : Type u) (_ : CommRing A) (I : Type u) (_ : Infinite I) (A_ : I → Type u)
      (_ : ∀ i, CommRing (A_ i)) (_ : ∀ i, Algebra A (A_ i)),
      (∀ i, Module.Flat A (A_ i)) ∧
        (∀ (M : Type u) [AddCommGroup M] [Module A M], Module.IsPiTensorEqualizer A A_ M) ∧
          ∀ (J : Finset I), ¬ ∀ (M : Type u) [AddCommGroup M] [Module A M],
            Module.IsPiTensorEqualizer A (fun j : J ↦ A_ (j : I)) M)
