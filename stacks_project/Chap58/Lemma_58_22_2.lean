/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtaleNeighborhood
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/-- The reduced closed subscheme with support the closure of `V(f) ∩ U` in the
punctured spectrum `U` of `A`, rather than the possibly nonreduced principal
quotient punctured spectrum. -/
def puncturedPrincipalSupport {A : Type u} [CommRing A] [IsLocalRing A]
    (f : maximalIdeal A) : (scheme A).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure
      {x : scheme A |
        x.val ∈
          PrimeSpectrum.zeroLocus (Ideal.span ({(f : A)} : Set A) : Set A)})

/- Lemma 58.22.2: in Situation 58.19.1, if `A` has a dualizing complex and is
`f`-adically complete, and every irreducible component of `X = Spec A` not
contained in `X0 = V(f)` has dimension at least `3`, then the restriction
functor `colim_{U0 ⊂ U' ⊂ U open} FÉt_{U'} ⟶ FÉt_{U0}` is fully faithful. This
is restriction to `U0 = PuncturedSpectrum.scheme (A ⧸ principalIdeal (f : A))`,
with its actual principal-quotient scheme structure. -/
@[stacks 0DXX] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleRestriction_fullyFaithful :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (f : maximalIdeal A)
      (h_dualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizing)
      [IsAdicComplete (Ideal.span ({(f : A)} : Set A)) A]
      (h_dim : ∀ p : PrimeSpectrum A, p.asIdeal ∈ minimalPrimes A →
        (f : A) ∉ p.asIdeal → (3 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal))
      (t : ColimitCocone
        (Scheme.finiteEtaleNeighborhoodDiagram (principalQuotientMap f).ker)),
      Nonempty (principalNeighborhoodRestriction f t).FullyFaithful)

end AlgebraicGeometry.PuncturedSpectrum
