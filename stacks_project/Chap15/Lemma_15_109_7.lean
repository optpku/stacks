module

import StacksCheckRecall
public import ReasLib.RingTheory.AdicCompletion.Branches

/-!
# Lemma 15.109.7

@stack 0C2D
-/

@[expose] public section

open IsLocalRing

universe u v w

/- Lemma 15.109.7 (1): for a one-dimensional Noetherian local ring, the
number of branches is unchanged by maximal-ideal completion.  This historical
snapshot is the current Stacks Lemma 15.110.7, tag `0C2D`. -/
@[stacks 0C2D "Lemma 15.109.7 (1)"]
#check fun (A : Type u) (Ah : Type v) (Ahat : Type w)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
    [CommRing Ahat]
    [Algebra (AdicCompletion (maximalIdeal A) A) Ahat]
    [IsHenselizationOf (AdicCompletion (maximalIdeal A) A) Ahat]
    (hdim : ringKrullDim A = 1) ↦
  (BranchNumber.eq_completion_of_ringKrullDim_eq_one
      (A := A) (Ah := Ah) (Ahat := Ahat) hdim :
    branchNumber A Ah =
      branchNumber (AdicCompletion (maximalIdeal A) A) Ahat)

/- Lemma 15.109.7 (2): for a one-dimensional Noetherian local ring, the
number of geometric branches is unchanged by maximal-ideal completion.  This
historical snapshot is the current Stacks Lemma 15.110.7, tag `0C2D`. -/
@[stacks 0C2D "Lemma 15.109.7 (2)"]
#check fun (A : Type u) (Ash : Type v) (Ahatsh : Type w)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [CommRing Ahatsh]
    [Algebra (AdicCompletion (maximalIdeal A) A) Ahatsh]
    [IsStrictHenselizationOf (AdicCompletion (maximalIdeal A) A) Ahatsh]
    (hdim : ringKrullDim A = 1) ↦
  (GeometricBranchNumber.eq_completion_of_ringKrullDim_eq_one
      (A := A) (Ash := Ash) (Ahatsh := Ahatsh) hdim :
    geometricBranchNumber A Ash =
      geometricBranchNumber (AdicCompletion (maximalIdeal A) A) Ahatsh)
