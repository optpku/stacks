module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.OneAdd
public import stacks_project.Chap88.Definition_88_18_1_Ring
public import stacks_project.Chap88.Lemma_88_3_2_Presentation

/-!
# Finite-type smoothness away from V(I) versus rig-smoothness of the completion

Lemma 88.4.3 compares smoothness of Spec B → Spec A over Spec A \ V(I)
with rig-smoothness of the I-adic completion B^∧.
-/

@[expose] public section

universe u

open Algebra.NaiveCotangent.Adic
open PrimeSpectrum

namespace Algebra

/-- Smoothness of Spec B → Spec A over Spec A \ V(I), as containment of the
complement of `zeroLocus (I.map (algebraMap A B))` in `smoothLocus A B`. -/
def IsSmoothOverComplement {A : Type u} [CommRing A] (I : Ideal A)
    (B : Type u) [CommRing B] [Algebra A B] : Prop :=
  (zeroLocus (I.map (algebraMap A B) : Set B))ᶜ ⊆ smoothLocus A B

/-- Unfolding of `IsSmoothOverComplement` as containment of the complement of
`V(I B)` in the smooth locus. -/
theorem isSmoothOverComplement_iff {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (I : Ideal A) :
    IsSmoothOverComplement I B ↔
      (zeroLocus (I.map (algebraMap A B) : Set B))ᶜ ⊆ smoothLocus A B :=
  sorry

/-- Over a Noetherian ring, smoothness over Spec A \ V(I) is equivalent to
smoothness of each principal localization `B_g` for `g ∈ I B`. -/
theorem isSmoothOverComplement_iff_forall_mem_map_smooth
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (I : Ideal A) :
    IsSmoothOverComplement I B ↔
      ∀ g ∈ I.map (algebraMap A B), Smooth A (Localization.Away g) :=
  sorry

namespace RigSmooth

/-- Lemma 88.4.3 (1). Let `A` be a Noetherian ring and let `I` be an ideal.
Let `B` be a finite type `A`-algebra. If Spec B → Spec A is smooth over
Spec A \ V(I), then `algebraCompletion I B` is rig-smooth over `(A, I)`. -/
@[stacks 0GAK]
theorem of_isSmoothOverComplement {A B : Type u} [CommRing A]
    [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (I : Ideal A) (h : IsSmoothOverComplement I B) :
    RigSmooth I (algebraCompletion I B) :=
  sorry

/-- Lemma 88.4.3 (2). Let `A` be a Noetherian ring and let `I` be an ideal.
Let `B` be a finite type `A`-algebra. If `algebraCompletion I B` is
rig-smooth over `(A, I)`, then there exists `g ∈ (I.map (algebraMap A B)).oneAdd`
such that Spec(`Localization.Away g`) is smooth over Spec A \ V(I). -/
@[stacks 0GAK]
theorem exists_mem_oneAdd_isSmoothOverComplement {A B : Type u} [CommRing A]
    [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (I : Ideal A) [RigSmooth I (algebraCompletion I B)] :
    ∃ g : B, g ∈ (I.map (algebraMap A B)).oneAdd ∧
      IsSmoothOverComplement I (Localization.Away g) :=
  sorry

end RigSmooth

end Algebra
