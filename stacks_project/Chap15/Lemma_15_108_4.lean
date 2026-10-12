/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Henselian.StrictHenselization.TensorProduct.MinimalPrime

/-!
@stack 06DU
-/

@[expose] public section

open IsLocalRing
open IsStrictHenselizationOf.TensorProduct
open scoped TensorProduct

universe u v w x

/- Lemma 15.108.4: let `k` be a field, let `A` and `B` be strictly henselian local `k`-algebras
whose residue fields are identified with `k`, and let `C`
be a strict henselization of the localization of `A ⊗[k] B` at the closed
point.  The minimal primes of `C` correspond bijectively to pairs of minimal
primes of `A` and `B`.  The historical snapshot uses tag `06DU`, currently
listed by Stacks as Lemma 15.109.4. -/
@[stacks 06DU "Lemma 15.108.4"]
#check fun (k : Type u) (A : Type v) (B : Type w) (C : Type x)
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [StrictHenselianLocalRing A] [StrictHenselianLocalRing B]
    (hκA : ResidueField A ≃ₐ[k] k) (hκB : ResidueField B ≃ₐ[k] k)
    [CommRing C] [Algebra (localization hκA hκB) C]
    [IsStrictHenselizationOf (localization hκA hκB) C] ↦
  (bijective_minimalPrimes hκA hκB :
    Function.Bijective
      (fun r : minimalPrimes C ↦ minimalPrimePair hκA hκB r))

end
