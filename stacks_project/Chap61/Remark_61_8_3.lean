/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.IndEtaleEnvelope.Functoriality
import StacksCheckRecall

@[expose] public section

universe u

/- Remark 61.8.3: a ring map `φ : A →+* A'` induces a ring map
`T(A) → T(A')`, where `T(A) = IndEtaleEnvelope A` is the colimit of finite
tensors of faithfully flat standard-smooth relative-dimension-0 presentations,
making the square with the base-to-envelope structure maps commute. -/
@[stacks 097T] #check
  (Algebra.IndEtaleEnvelope.map_commSq :
    ∀ {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A'),
      CategoryTheory.CommSq
        (CommRingCat.ofHom (Algebra.algebraMap A
          (Algebra.IndEtaleEnvelope A)))
        (CommRingCat.ofHom φ)
        (CommRingCat.ofHom (Algebra.IndEtaleEnvelope.map φ))
        (CommRingCat.ofHom (Algebra.algebraMap A'
          (Algebra.IndEtaleEnvelope A'))))
