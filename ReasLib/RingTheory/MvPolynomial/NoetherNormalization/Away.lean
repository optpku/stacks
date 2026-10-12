/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.NoetherNormalization
public import ReasLib.RingTheory.KrullDimension.FiniteType.Local

@[expose] public section

/-!
# Local Noether normalization on a basic open

@stack 00OZ

The witness retains the basic-open element, the number of variables, and the
finite injective polynomial map as concrete data.
-/

open TopologicalSpace Topology

universe u v

namespace MvPolynomial.NoetherNormalization.Away

variable {k : Type u} {S : Type v} [Field k] [CommRing S] [Algebra k S]

/-- A witness that `Localization.Away g` realizes the local dimension at `x`
and admits a finite injective polynomial normalization by `d` variables. -/
@[stacks 00OZ "local Noether normalization witness"]
structure IsAtPoint
    (x : PrimeSpectrum S) (g : S) (d : ℕ)
    (f : MvPolynomial (Fin d) k →ₐ[k] Localization.Away g) : Prop where
  not_mem_asIdeal : g ∉ x.asIdeal
  ringKrullDim_eq : ringKrullDim (Localization.Away g) = d
  topologicalKrullDimAt_eq : topologicalKrullDimAt x = d
  injective : Function.Injective f
  finite : AlgHom.Finite f

/-- The directly consumable specification of a local Noether normalization
witness. -/
@[stacks 00OZ "local Noether normalization specification"]
theorem isAtPoint_iff
    (x : PrimeSpectrum S) (g : S) (d : ℕ)
    (f : MvPolynomial (Fin d) k →ₐ[k] Localization.Away g) :
    IsAtPoint x g d f ↔
      g ∉ x.asIdeal ∧
        ringKrullDim (Localization.Away g) = d ∧
          topologicalKrullDimAt x = d ∧ Function.Injective f ∧ AlgHom.Finite f := sorry

/-- Lemma 10.115.5 (00OZ): every point of a finite-type affine algebra over a
field has a basic-open neighborhood with a finite injective polynomial
normalization realizing its local dimension. -/
@[stacks 00OZ]
theorem exists_at_point [Algebra.FiniteType k S] (x : PrimeSpectrum S) :
    ∃ (g : S) (d : ℕ) (f : MvPolynomial (Fin d) k →ₐ[k] Localization.Away g),
      IsAtPoint x g d f := sorry

end MvPolynomial.NoetherNormalization.Away
