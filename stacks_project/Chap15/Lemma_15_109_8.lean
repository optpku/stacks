/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.Branches.FormalFiber
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.109.8 (0C2E)

@stack 0C2E
-/

open IsLocalRing

universe u v w

-- Lemma 15.109.8 (1), geometrically normal formal fibers imply the Nagata property.
section

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

@[stacks 0C2E "Lemma 15.109.8 (1)"]
#check fun (hA : FieldAlgebraProperty.geometricallyNormal.HoldsOnFormalFibers A) ↦
  (NagataRing.of_geometricallyNormalFormalFibers A hA : NagataRing A)

end

-- Lemma 15.109.8 (2), ordinary branch count is preserved by completion.
section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {Ah : Type v} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]

@[stacks 0C2E "Lemma 15.109.8 (2)"]
#check fun (hA : FieldAlgebraProperty.geometricallyNormal.HoldsOnFormalFibers A) ↦
  (BranchNumber.eq_completion_minimalPrimes_of_geometricallyNormalFormalFibers
      (Ah := Ah) hA :
    branchNumber A Ah =
      (minimalPrimes (AdicCompletion (maximalIdeal A) A)).encard)

end

-- Lemma 15.109.8 (3), geometric branch count is preserved by completion.
section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable {Ash : Type v} [CommRing Ash] [Algebra A Ash]
variable [IsStrictHenselizationOf A Ash]
variable {Ahatsh : Type w} [CommRing Ahatsh]
variable [Algebra (AdicCompletion (maximalIdeal A) A) Ahatsh]
variable [IsStrictHenselizationOf (AdicCompletion (maximalIdeal A) A) Ahatsh]

@[stacks 0C2E "Lemma 15.109.8 (3)"]
#check fun (hA : FieldAlgebraProperty.geometricallyNormal.HoldsOnFormalFibers A) ↦
  (GeometricBranchNumber.eq_completion_of_geometricallyNormalFormalFibers
      (Ash := Ash) (Ahatsh := Ahatsh) hA :
    geometricBranchNumber A Ash =
      geometricBranchNumber (AdicCompletion (maximalIdeal A) A) Ahatsh)

end
