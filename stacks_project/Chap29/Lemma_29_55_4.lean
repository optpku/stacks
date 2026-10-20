/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Seminormalization.Localization
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.55.4

Let `A → B` be a ring map inducing a dominant morphism `Spec(B) → Spec(A)`. Formation of
the maximal seminormalization subalgebra of `B` over `A` commutes with localization.
-/
@[stacks 0H3M] #check
  (AlgebraicGeometry.UniversalHomeomorphism.maximalSeminormalizationSubalgebra_localization_eq :
    ∀ {A B Aₛ Bₛ : Type u} [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₛ]
      [Algebra A B] {S : Submonoid A} [Algebra A Aₛ] [IsLocalization S Aₛ]
      [Algebra B Bₛ] [IsLocalization (Algebra.algebraMapSubmonoid B S) Bₛ]
      [Algebra Aₛ Bₛ] [Algebra A Bₛ] [IsScalarTower A B Bₛ] [IsScalarTower A Aₛ Bₛ],
        IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A B))) →
          ∀ (B' : Subalgebra A B),
            AlgebraicGeometry.UniversalHomeomorphism.IsMaximalSeminormalizationSubalgebra B' →
              ∀ (Bₛ' : Subalgebra Aₛ Bₛ),
                AlgebraicGeometry.UniversalHomeomorphism.IsMaximalSeminormalizationSubalgebra Bₛ' →
                  Algebra.adjoin Aₛ ((algebraMap B Bₛ) '' (B' : Set B)) = Bₛ')
