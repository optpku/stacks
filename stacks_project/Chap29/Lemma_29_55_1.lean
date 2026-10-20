/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.WeakNormalization
import StacksCheckRecall

universe u

/- Lemma 29.55.1: if a ring map `A → B` induces a dominant morphism
`Spec(B) → Spec(A)`, then there is an `A`-subalgebra `B' ⊆ B` whose affine spectrum maps to
`Spec(A)` by a universal homeomorphism, and every factorization `A → C → B` through a ring `C`
whose spectrum is universally homeomorphic to `Spec(A)` has image contained in `B'`. -/
@[stacks 0H3J] #check
  (AlgebraicGeometry.UniversalHomeomorphism.exists_maximalSubalgebra_of_isDominantSpecMap :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B],
      AlgebraicGeometry.IsDominant
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B))) →
        ∃ B' : Subalgebra A B,
          AlgebraicGeometry.UniversalHomeomorphism
              (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B'))) ∧
            ∀ {C : Type u} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B],
              AlgebraicGeometry.UniversalHomeomorphism
                  (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A C))) →
                ∀ c : C, algebraMap C B c ∈ B')
