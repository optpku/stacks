module

public import ReasLib.RingTheory.Etale.Counterexample.CotangentComplex
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 110.43.1: there exists a formally étale surjective ring map with nontrivial
André-Quillen cotangent complex. -/
@[stacks 06E6] #check (RingHom.exists_formallyEtale_surjective_cotangentComplex_ne_zero :
  ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (f : A →+* B),
    f.FormallyEtale ∧ Function.Surjective f ∧
      ∃ n : ℤ, ¬ CategoryTheory.Limits.IsZero ((RingHom.cotangentComplex f).homology n))
