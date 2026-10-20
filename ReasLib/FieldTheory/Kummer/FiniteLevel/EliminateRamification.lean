/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution
public import ReasLib.FieldTheory.Kummer.FiniteLevel.BaseChange
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.TotalRamification
public import ReasLib.FieldTheory.PurelyInseparable.PowerIntersection
public import Mathlib.Algebra.CharP.MixedCharZero
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Kummer finite-level ramification elimination

This module owns the reusable alternatives used by Lemmas 15.116.15 and 15.116.16.  The source
chapter files are recall surfaces; the finite-level predicates, reduced tensor base-change views,
and total-ramification owner live in the shared Kummer/DVR API.

@stack 09F4
@stack 09F5
-/

open scoped TensorProduct
open Polynomial
open IsExtensionOfDiscreteValuationRings
open IsLocalRing
open DVR.Field

universe u v w x y z u'

namespace KummerArtinSchreier.FiniteLevel.BaseChange

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable {p : ℕ} [Fact p.Prime] [MixedCharZero A p]
variable {K : Type x} {L : Type y} {M : Type z}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field M] [Algebra A M] [Algebra B M] [Algebra C M] [IsFractionRing C M]
variable [Algebra L M] [Algebra K M]
variable [IsScalarTower A C M] [IsScalarTower A K M]
variable [IsScalarTower B C M] [IsScalarTower B L M] [IsScalarTower K L M]
variable [IsGalois L M]

/-- Lemma 15.116.15: if `A ⊆ B ⊆ C` are extensions of discrete valuation rings with fraction
fields `K ⊆ L ⊆ M`, `A` has mixed characteristic `(0, p)`, `A ⊆ B` is weakly unramified, `B`
contains a primitive `p`th root of unity, and `M / L` is Galois of degree `p`, then there exists a
finite Galois extension `K₁ / K` totally ramified with respect to `A` such that either `K₁ / K`
is a weak solution for `A → C`, or the global tensor base change satisfies the shared
finite-level owner. -/
@[stacks 09F4 "Lemma 15.116.15: finite-level base change alternative"]
theorem exists_totallyRamified
    (hAB : WeaklyUnramified A B)
    (hζ : ∃ ζ : B, IsPrimitiveRoot ζ p)
    (hdeg : Module.finrank L M = p) :
    -- Local instance justification (proof-local temporary data): the tower supplies the canonical
    -- composite DVR extension only while interpreting the weak-solution alternative.
    let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
    ∃ (K1 : Type u') (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsGalois K K1 ∧
        IsTotallyRamified A K K1 ∧
          (IsWeakSolutionFor A C K M K1 ∨
            KummerArtinSchreier.FiniteLevel.IsExtension.OnBaseChange
              B K L M p K1) := sorry
-- Proof strategy: use the primitive root in `B` and Kummer theory to choose a generating
-- Kummer--Artin--Schreier equation for the degree-`p` Galois extension `M / L`.  Normalize its
-- denominator over the weakly-unramified DVR `B`.  Adjoin to `K` a finite Galois totally ramified
-- extension that matches the required denominator valuation.  Analyze every normalized reduced
-- tensor branch: if all branch maximal ideals descend, package `IsWeakSolutionFor`; otherwise the
-- surviving branch equation satisfies `RootEquation.IsFiniteLevel`, and the normalization support
-- gives `FiniteLevel.IsExtension.OnBaseChange`.

/-- Downstream view of the 09F4 alternative when the composite extension `A → C` is already
available as a canonical instance. -/
@[stacks 09F4 "finite-level base change with an explicit composite DVR extension"]
theorem exists_totallyRamified_of_extension
    [IsExtensionOfDiscreteValuationRings A C]
    (hAB : WeaklyUnramified A B)
    (hζ : ∃ ζ : B, IsPrimitiveRoot ζ p)
    (hdeg : Module.finrank L M = p) :
    ∃ (K1 : Type u') (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsGalois K K1 ∧
        IsTotallyRamified A K K1 ∧
          (IsWeakSolutionFor A C K M K1 ∨
            KummerArtinSchreier.FiniteLevel.IsExtension.OnBaseChange
              B K L M p K1) := sorry
-- Proof strategy: apply `exists_totallyRamified` using the tower-derived composite extension
-- `of_tower A B C`; identify it with the supplied `IsExtensionOfDiscreteValuationRings A C`
-- instance by proof irrelevance and reuse the same existential field and branch witnesses.

end

end KummerArtinSchreier.FiniteLevel.BaseChange

namespace KummerArtinSchreier.FiniteLevel.Descent

noncomputable section

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable {p : ℕ} [Fact p.Prime] [MixedCharZero A p]
variable {K : Type x} {L : Type y} {M : Type z}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
variable [Field M] [Algebra A M] [Algebra B M] [Algebra C M] [IsFractionRing C M]
variable [Algebra L M] [Algebra K M]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [IsScalarTower A C M] [IsScalarTower A K M] [IsScalarTower B C M] [IsScalarTower B L M]
variable [IsScalarTower K L M]

/-- Lemma 15.116.16: let `A ⊆ B ⊆ C` be extensions of discrete valuation rings with fraction
fields `K ⊆ L ⊆ M`. Assume mixed characteristic `(0, p)`, weak unramifiedness of `A ⊆ B`, a
degree-`p` extension `M / L` of finite level `l > 0`, and that the residue-field image is the
stable positive `p`-power intersection. Then a finite separable totally ramified extension `K₁ / K`
either gives a weak solution for `A → C`, or lowers the exact finite level after global base
change. The primitive-root and degree-`p` conditions are bundled by `FiniteLevel.IsAtLevel`. -/
@[stacks 09F5 "Lemma 15.116.16: finite-level descent"]
theorem exists_totallyRamified
    {l : ℚ} (hl : 0 < l)
    (hAB : WeaklyUnramified A B)
    (hLM : KummerArtinSchreier.FiniteLevel.IsAtLevel B L M p l)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        PerfectClosure.powerIntersection (ResidueField B) p) :
    -- Local instance justification (proof-local temporary data): the tower supplies the canonical
    -- composite DVR extension only while interpreting the weak-solution alternative.
    let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
    ∃ (K1 : Type u') (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsTotallyRamified A K K1 ∧
        Algebra.IsSeparable K K1 ∧
          (IsWeakSolutionFor A C K M K1 ∨
            ∃ l' : ℚ,
              KummerArtinSchreier.FiniteLevel.IsAtLevel.OnBaseChange
                B K L M p l' K1 ∧
                l' ≤ max 0 (max (l - 1) (2 * l - p))) := sorry
-- Proof strategy: choose the normalized minimal presentation carried by `hLM` and write its level
-- as `n / e`.  Use `hκ` and `PerfectClosure.mem_powerIntersection_iff` to approximate the residue
-- numerator by a sufficiently deep `p`th power coming from `ResidueField A`, then lift that
-- approximation to the DVR.  Construct the corresponding finite separable totally ramified Kummer
-- extension `K1 / K`.  Apply the quotient-polynomial and scaled-law power-lattice congruences on
-- every reduced tensor branch.  Either all branch maximal ideals descend, giving
-- `IsWeakSolutionFor`, or normalize the transformed equation and compute its new ratio `l'`; the
-- two possible valuation minima give `l' ≤ max 0 (max (l - 1) (2 * l - p))` and package the global
-- exact-level normalization.

/-- Downstream view of the 09F5 descent statement when the composite extension `A → C` is already
available as a canonical instance. -/
@[stacks 09F5 "finite-level descent with an explicit composite DVR extension"]
theorem exists_totallyRamified_of_extension
    [IsExtensionOfDiscreteValuationRings A C]
    {l : ℚ} (hl : 0 < l)
    (hAB : WeaklyUnramified A B)
    (hLM : KummerArtinSchreier.FiniteLevel.IsAtLevel B L M p l)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        PerfectClosure.powerIntersection (ResidueField B) p) :
    ∃ (K1 : Type u') (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsTotallyRamified A K K1 ∧
        Algebra.IsSeparable K K1 ∧
          (IsWeakSolutionFor A C K M K1 ∨
            ∃ l' : ℚ,
              KummerArtinSchreier.FiniteLevel.IsAtLevel.OnBaseChange
                B K L M p l' K1 ∧
                l' ≤ max 0 (max (l - 1) (2 * l - p))) := sorry
-- Proof strategy: apply the primary descent theorem with the tower-derived composite DVR extension,
-- align it with the supplied `A → C` extension by proof irrelevance, and retain the constructed
-- totally ramified field, separability, weak-solution, and level-bound witnesses unchanged.

end

end

end KummerArtinSchreier.FiniteLevel.Descent
