/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Unramified.LocalStructure
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.144.6
@stack 00UG

The local standard-étale chart is owned by Mathlib.  This file keeps only the source-facing
finite flat extension and its primewise factorization property; the chartwise tensor-product
construction belongs to the proof stage.
-/

universe u v

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Etale R S]

/-- Lemma 10.144.6: if `R → S` is étale and `Spec(S) → Spec(R)` is surjective, then
there is a finite, finitely presented, flat `R`-algebra `S'` with surjective spectrum map such
that `R → S'[1/g']` factors through `S` near every prime of `S'`. -/
@[stacks 00UG]
theorem exists_finitePresentation_flat_surjective_localFactorization_extension
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S))) :
    ∃ (S' : Type (max u v)) (_ : CommRing S') (_ : Algebra R S')
      (_ : Module.Finite R S') (_ : Algebra.FinitePresentation R S')
      (_ : Module.Flat R S')
      (_ : Function.Surjective (PrimeSpectrum.comap (algebraMap R S'))),
        ∀ q' : PrimeSpectrum S',
          ∃ (g' : S') (_ : g' ∉ q'.asIdeal), Nonempty (S →ₐ[R] Localization.Away g') := sorry

end

end Algebra

@[stacks 00UG "standard-étale local chart"]
#check @Algebra.IsEtaleAt.exists_isStandardEtale

@[stacks 00UG "affine spectrum map"]
#check @PrimeSpectrum.comap

@[stacks 00UG "source-facing finite flat extension"]
#check @Algebra.exists_finitePresentation_flat_surjective_localFactorization_extension

end
