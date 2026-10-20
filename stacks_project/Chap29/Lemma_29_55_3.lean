/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Seminormalization.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

/- Lemma 29.55.3

Let `A → B` be a ring map inducing a dominant map `Spec(B) → Spec(A)`. There is an
`A`-subalgebra `B' ⊆ B` whose spectrum is universally homeomorphic to `Spec(A)` with unchanged
residue fields and which contains the image of every compatible intermediate algebra with these
properties.
-/
@[stacks 0H3L] #check
  (AlgebraicGeometry.UniversalHomeomorphism.exists_maximalSeminormalizationSubalgebra_of_isDominantSpecMap :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B],
      IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A B))) →
        ∃ B' : Subalgebra A B,
          AlgebraicGeometry.UniversalHomeomorphism
              (Spec.map (CommRingCat.ofHom (algebraMap A B'))) ∧
            (∀ x : Spec (CommRingCat.of B'),
              IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B'))).residueFieldMap x)) ∧
              ∀ {C : Type u} [CommRing C] [Algebra A C] [Algebra C B]
                  [IsScalarTower A C B],
                AlgebraicGeometry.UniversalHomeomorphism
                    (Spec.map (CommRingCat.ofHom (algebraMap A C))) →
                  (∀ x : Spec (CommRingCat.of C),
                    IsIso
                      ((Spec.map (CommRingCat.ofHom (algebraMap A C))).residueFieldMap x)) →
                    ∀ c : C, algebraMap C B c ∈ B')

end

end AlgebraicGeometry
