/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.TrivSqZeroExt

@[expose] public section

#check (DividedPowers.TrivSqZeroExt.ideal :
  ∀ {A : Type _} [CommRing A] (M : Type _) [AddCommGroup M] [Module A M]
    [Module Aᵐᵒᵖ M] [IsCentralScalar A M], Ideal A → Ideal (TrivSqZeroExt A M))

#check (DividedPowers.TrivSqZeroExt.mem_ideal_iff :
  ∀ {A : Type _} {M : Type _} [CommRing A] [AddCommGroup M] [Module A M]
    [Module Aᵐᵒᵖ M] [IsCentralScalar A M] (I : Ideal A) (a : TrivSqZeroExt A M),
    a ∈ DividedPowers.TrivSqZeroExt.ideal M I ↔ a.fst ∈ I)

#check (DividedPowers.TrivSqZeroExt.dpowPred :
  ∀ {A : Type _} [CommRing A] {I : Ideal A} (gamma : DividedPowers I)
    (n : ℕ) (x : A), A)

#check (DividedPowers.TrivSqZeroExt.dividedPowers_apply :
  ∀ {A : Type _} {M : Type _} [CommRing A] [AddCommGroup M] [Module A M]
    [Module Aᵐᵒᵖ M] [IsCentralScalar A M] {I : Ideal A} (gamma : DividedPowers I)
    (n : ℕ) (x : A) (hx : x ∈ I) (z : M),
    DividedPowers.TrivSqZeroExt.dividedPowers M gamma n
        (TrivSqZeroExt.inl x + TrivSqZeroExt.inr z) =
      TrivSqZeroExt.inl (gamma.dpow n x) +
        TrivSqZeroExt.inr (DividedPowers.TrivSqZeroExt.dpowPred gamma n x • z))

#check (DividedPowers.TrivSqZeroExt.inlDPMorphism_toRingHom :
  ∀ {A : Type _} [CommRing A] (M : Type _) [AddCommGroup M] [Module A M]
    [Module Aᵐᵒᵖ M] [IsCentralScalar A M] {I : Ideal A} (gamma : DividedPowers I),
    (DividedPowers.TrivSqZeroExt.inlDPMorphism M gamma).toRingHom =
      TrivSqZeroExt.inlHom A M)
