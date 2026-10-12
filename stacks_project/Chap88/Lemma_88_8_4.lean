/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.RingTheory.Ideal.OneAdd
public import stacks_project.Chap88.Definition_88_20_1_Ring
public import stacks_project.Chap88.Lemma_88_3_2_Presentation
public import stacks_project.Chap88.Lemma_88_8_4_EtaleOverComplement

/-!
# Completions of finite-type algebras étale away from V(I)

Lemma 88.8.4 relates étaleness of a finite-type algebra over `Spec(A) \ V(I)`
with rig-étaleness of its `I`-adic completion in the sense of Lemma 88.8.2.
-/

@[expose] public section

universe u

open Algebra Algebra.NaiveCotangent.Adic AlgebraicGeometry

namespace Algebra

/-- Under finite type over a Noetherian ring, étaleness over `Spec(A) \ V(I)` is
equivalent to étaleness of the restriction of `Spec.map (algebraMap A B)` to
that open. -/
theorem isEtaleOverComplement_iff_morphismRestrict {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [FiniteType A B] :
    IsEtaleOverComplement I B ↔
      AlgebraicGeometry.Etale
        (Spec.map (CommRingCat.ofHom (algebraMap A B)) ∣_
          ⟨(PrimeSpectrum.zeroLocus (I : Set A))ᶜ,
            (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩) :=
  sorry

end Algebra

namespace Algebra.RigEtale

/-- Lemma 88.8.4 (1): Let `A` be a Noetherian ring and let `I` be an ideal. Let
`B` be a finite type `A`-algebra. If `Spec(B) → Spec(A)` is étale over
`Spec(A) \ V(I)`, then the `I`-adic completion `B^∧` is rig-étale over `(A, I)`
in the sense of Lemma 88.8.2. -/
@[stacks 0ALQ]
theorem of_isEtaleOverComplement {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B] [FiniteType A B]
    (h : IsEtaleOverComplement I B) :
    RigEtale I (algebraCompletion I B) :=
  sorry

/-- Lemma 88.8.4 (2): Let `A` be a Noetherian ring and let `I` be an ideal. Let
`B` be a finite type `A`-algebra. If the `I`-adic completion `B^∧` is rig-étale
over `(A, I)` in the sense of Lemma 88.8.2, then there exists
`g ∈ (I.map (algebraMap A B)).oneAdd` such that `Spec(B_g)` is étale over
`Spec(A) \ V(I)`. -/
@[stacks 0ALQ]
theorem exists_mem_oneAdd_isEtaleOverComplement {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) (B : Type u) [CommRing B] [Algebra A B]
    [FiniteType A B] [RigEtale I (algebraCompletion I B)] :
    ∃ g ∈ (I.map (algebraMap A B)).oneAdd,
      IsEtaleOverComplement I (Localization.Away g) :=
  sorry

end Algebra.RigEtale
