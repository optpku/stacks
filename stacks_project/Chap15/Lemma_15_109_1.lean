/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.Branches.Comparison
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.109.1 (0C28)

@stack 0C28
-/

open IsLocalRing

universe u v w

-- Lemma 15.109.1 (1), surjectivity on minimal primes from the completion to a henselization.
section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

@[stacks 0C28 "Lemma 15.109.1 (1)"]
#check fun
    (iota : IsHenselizationOf.Completion.Comparison (R := A) (Rh := Ah)) ↦
  (IsHenselizationOf.Completion.Comparison.minimalPrimeMap_surjective iota :
    Function.Surjective
      (IsHenselizationOf.Completion.Comparison.minimalPrimeMap iota))

end

-- Lemma 15.109.1 (2), branch number does not decrease under completion.
section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

@[stacks 0C28 "Lemma 15.109.1 (2)"]
#check (BranchNumber.le_completion (A := A) (Ah := Ah) :
  branchNumber A Ah ≤
    (minimalPrimes (AdicCompletion (maximalIdeal A) A)).encard)

end

-- Lemma 15.109.1 (3), geometric branch number does not decrease under completion.
section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {Ash : Type v} [CommRing Ash] [Algebra A Ash]
variable [IsStrictHenselizationOf A Ash]
variable {Ahatsh : Type w} [CommRing Ahatsh]
variable [Algebra (AdicCompletion (maximalIdeal A) A) Ahatsh]
variable [IsStrictHenselizationOf (AdicCompletion (maximalIdeal A) A) Ahatsh]

@[stacks 0C28 "Lemma 15.109.1 (3)"]
#check (GeometricBranchNumber.le_completion (A := A) (Ash := Ash) (Ahatsh := Ahatsh) :
  geometricBranchNumber A Ash ≤
    geometricBranchNumber (AdicCompletion (maximalIdeal A) A) Ahatsh)

end
