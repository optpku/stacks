/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.CotangentComplex.Surjective

/-!
# Cotangent homology of a surjective ring map
-/

@[expose] public section

universe u

/- Lemma 92.11.2. The degree-zero homology of the cotangent complex of a surjective
ring map vanishes. -/
@[stacks 08RA] #check (Algebra.CotangentComplex.homology_zero_isZero_of_surjective :
  ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B],
    Function.Surjective (algebraMap A B) →
      CategoryTheory.Limits.IsZero ((Algebra.cotangentComplex A B).homology 0))

/- Lemma 92.11.2. The canonical comparison from the kernel modulo its square to
degree-minus-one cotangent homology, induced by the empty polynomial presentation,
is an isomorphism. -/
@[stacks 08RA] #check (Algebra.CotangentComplex.homology_negOne_iso_of_surjective :
  ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (h : Function.Surjective (algebraMap A B)),
    CategoryTheory.IsIso (Algebra.CotangentComplex.homology_negOne_conormal_comparison h))
