/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.WeakNormalization
import StacksCheckRecall

universe u

/- Lemma 29.55.2: let `A → B` be a ring map inducing a dominant morphism
`Spec(B) → Spec(A)`. For any multiplicative subset `S ⊆ A`, formation of the maximal
intermediate subalgebra whose spectrum is universally homeomorphic to the base commutes with
localization. -/
@[stacks 0H3K] #check
  (AlgebraicGeometry.UniversalHomeomorphism.weakNormalizationSubalgebra_localization_eq :
    ∀ {A B Aₛ Bₛ : Type u} [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₛ]
      [Algebra A B] {S : Submonoid A} [Algebra A Aₛ] [IsLocalization S Aₛ]
      [Algebra B Bₛ] [IsLocalization (Algebra.algebraMapSubmonoid B S) Bₛ]
      [Algebra Aₛ Bₛ] [Algebra A Bₛ] [IsScalarTower A B Bₛ] [IsScalarTower A Aₛ Bₛ],
      AlgebraicGeometry.IsDominant
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B))) →
        ∀ B' : Subalgebra A B,
          AlgebraicGeometry.UniversalHomeomorphism
              (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B'))) →
            (∀ {C : Type u} [CommRing C] [Algebra A C] [Algebra C B]
                [IsScalarTower A C B],
              AlgebraicGeometry.UniversalHomeomorphism
                  (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A C))) →
                ∀ c : C, algebraMap C B c ∈ B') →
              ∀ Bₛ' : Subalgebra Aₛ Bₛ,
                AlgebraicGeometry.UniversalHomeomorphism
                    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Aₛ Bₛ'))) →
                  (∀ {C : Type u} [CommRing C] [Algebra Aₛ C] [Algebra C Bₛ]
                      [IsScalarTower Aₛ C Bₛ],
                    AlgebraicGeometry.UniversalHomeomorphism
                        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Aₛ C))) →
                      ∀ c : C, algebraMap C Bₛ c ∈ Bₛ') →
                    Algebra.adjoin Aₛ ((algebraMap B Bₛ) '' (B' : Set B)) = Bₛ')
