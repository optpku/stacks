/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.LocalMap.Etale
import StacksCheckRecall

@[expose] public section

open IsLocalRing

universe u v

/- Lemma 41.11.3 (1): for an essentially finite type local homomorphism of Noetherian local
rings, essential étaleness is equivalent to essential étaleness of the induced map on
maximal-ideal completions, and also to ordinary étaleness of that completion map. -/
@[stacks 039M]
#check (AdicCompletion.LocalMap.etale_tfae :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f], f.EssFiniteType →
      List.TFAE [
        f.EssEtale,
        (AdicCompletion.mapLocal f).EssEtale,
        (AdicCompletion.mapLocal f).Etale])

/- Lemma 41.11.3 (2): under the equivalent étaleness conditions, the completed target is
linearly equivalent over the completed source to a nonzero finite direct sum of copies of the
completed source. -/
@[stacks 039M]
#check (AdicCompletion.LocalMap.exists_linearEquiv_of_essEtale :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f], f.EssFiniteType → f.EssEtale →
      letI : Algebra (AdicCompletion (maximalIdeal A) A)
          (AdicCompletion (maximalIdeal B) B) :=
        AdicCompletion.mapLocalAlgebra f
      ∃ n : ℕ, 1 ≤ n ∧
        Nonempty
          (AdicCompletion (maximalIdeal B) B ≃ₗ[AdicCompletion (maximalIdeal A) A]
            Fin n →₀ AdicCompletion (maximalIdeal A) A))
