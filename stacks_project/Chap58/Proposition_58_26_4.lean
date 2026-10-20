/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FormallySmooth
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FormallySmooth
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped ENat

universe u

/- Proposition 58.26.4 (1): if `A → B` is a local homomorphism of Noetherian local rings,
`A` has depth at least `2`, `A → B` is formally smooth for the `m_B`-adic topology, and
`dim B > dim A`, then for any open `V ⊂ Y = Spec B` containing every prime `q ⊂ B` with
`q ∩ A ≠ m_A` and also containing the prime `m_A B`, restriction `FÉt_Y ⥤ FÉt_V` is an
equivalence. -/
@[stacks 0EYC] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_isEquivalence_of_formallySmoothDepth :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hdepth : (2 : ℕ∞) ≤ moduleDepth A A)
    (hfs : (algebraMap A B).formally_smooth_for_adic (IsLocalRing.maximalIdeal B))
    (hdim : ringKrullDim A < ringKrullDim B)
    (V : (Spec (CommRingCat.of B)).Opens)
    (hV : ∀ q : PrimeSpectrum B,
      Ideal.comap (algebraMap A B) q.asIdeal ≠ IsLocalRing.maximalIdeal A ∨
        q.asIdeal = Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) →
      q ∈ V),
    Functor.IsEquivalence (Scheme.finiteEtaleBaseChange V.ι))

/- Proposition 58.26.4 (2): under the same hypotheses, purity holds for `B`. -/
@[stacks 0EYC] #check
  (AlgebraicGeometry.PuncturedSpectrum.hasPurity_of_formallySmoothDepth :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hdepth : (2 : ℕ∞) ≤ moduleDepth A A)
    (hfs : (algebraMap A B).formally_smooth_for_adic (IsLocalRing.maximalIdeal B))
    (hdim : ringKrullDim A < ringKrullDim B),
    PuncturedSpectrum.HasPurity B)
