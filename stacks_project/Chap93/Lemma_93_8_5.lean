/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Derivation.FiniteDimensional
public import ReasLib.RingTheory.Extension.Cotangent.FiniteDimensional
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 93.8.5: for a finite type algebra `P` over a field `k`, the vector space of
self-valued derivations is finite-dimensional exactly when every prime ideal of `P` is maximal.
For nontrivial `P`, this is equivalent to `ringKrullDim P = 0`. The zero algebra also satisfies
the criterion, but mathlib assigns it Krull dimension `⊥`, not `0`. The first cotangent extension
group is finite-dimensional when the nonsmooth locus has finitely many prime-spectrum points. -/
/- Lemma 93.8.5 (1): the derivation criterion. -/
@[stacks 0DY4] #check (Derivation.finiteDimensional_iff_krullDimLE_zero :
  ∀ (k : Type u) [Field k] (P : Type u) [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P],
    FiniteDimensional k (Derivation k P P) ↔ Ring.KrullDimLE 0 P)

/- Lemma 93.8.5 (2): finite-dimensionality under a finite nonsmooth locus. -/
@[stacks 0DY4] #check
  (RingHom.SquareZeroExtension.finiteDimensional_extOneNaiveCotangent_of_finite_nonsmooth :
    ∀ (k : Type u) [Field k] (P : Type u) [CommRing P] [Algebra k P]
      [Algebra.FiniteType k P]
      (_h : (Algebra.smoothLocus k P)ᶜ.Finite),
      FiniteDimensional k (RingHom.SquareZeroExtension.extOneNaiveCotangent k P P))

/- The literal dimension-equality formulation is valid for nontrivial algebras. -/
#check (Derivation.finiteDimensional_iff_ringKrullDim_eq_zero :
  ∀ (k : Type u) [Field k] (P : Type u) [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P] [Nontrivial P],
    FiniteDimensional k (Derivation k P P) ↔ ringKrullDim P = 0)
