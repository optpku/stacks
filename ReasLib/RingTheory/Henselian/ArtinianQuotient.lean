/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Basis.LocalRing
public import ReasLib.RingTheory.Henselian.FaithfullyFlat
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.Henselian.StrictHenselization.Composition
public import ReasLib.RingTheory.Henselian.FormallyEtale
public import ReasLib.RingTheory.RingHom.FormallyEtale.QuotientPow
import Mathlib.Tactic.CrossRefAttribute

/-!
# Artinian quotients of henselizations

This file records maximal-ideal-power comparisons for henselizations and the compatible bases of
the corresponding quotients of a strict henselization.

@stack 07QM
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u

namespace IsHenselizationOf

variable {R S : Type u} [CommRing R] [IsLocalRing R]
variable [CommRing S] [Algebra R S] [IsHenselizationOf R S]

/-- Lemma 15.45.1: a henselization induces a bijection on the quotients by every power of the
maximal ideal. -/
@[stacks 07QM "henselization maximal-ideal-power quotient comparison"]
theorem quotientPowMap_bijective (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap ((maximalIdeal S) ^ n) (algebraMap R S)
        (RingHom.IsLocalHom.pow_maximalIdeal_le_comap (algebraMap R S) n)) := sorry

end IsHenselizationOf

namespace IsStrictHenselizationOf

variable {R S : Type u} [CommRing R] [IsLocalRing R]
variable [CommRing S] [Algebra R S] [IsStrictHenselizationOf R S]

/-- The canonical algebra structure on corresponding maximal-ideal-power quotients of a strict
henselization. -/
@[stacks 07QM "strict-henselization quotient algebra", implicit_reducible]
noncomputable def quotientPowAlgebra (n : ℕ) :
    Algebra (R ⧸ (maximalIdeal R) ^ n) (S ⧸ (maximalIdeal S) ^ n) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (RingHom.IsLocalHom.pow_maximalIdeal_le_comap (algebraMap R S) n)

/-- Lemma 15.45.1: one family of elements of a strict henselization induces a basis on every
maximal-ideal-power quotient. -/
@[stacks 07QM "compatible bases on strict-henselization quotients"]
theorem exists_quotientPow_basis_lifts :
    ∃ (ι : Type u) (x : ι → S), ∀ n : ℕ,
      -- Local instance justification: each stage uses the explicit quotient algebra induced by
      -- the fixed strict-henselization map; it is not a global algebra choice.
      letI : Algebra (R ⧸ (maximalIdeal R) ^ n) (S ⧸ (maximalIdeal S) ^ n) :=
        quotientPowAlgebra (R := R) (S := S) n
      ∃ b : Module.Basis ι (R ⧸ (maximalIdeal R) ^ n) (S ⧸ (maximalIdeal S) ^ n),
        ∀ i, b i = Ideal.Quotient.mk _ (x i) := sorry

section Tower

variable {Rh : Type u} [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [Algebra Rh S] [IsScalarTower R Rh S] [IsStrictHenselizationOf Rh S]

/-- Lemma 15.45.1: in a strict henselization over a henselization, extending the base maximal
ideal directly or through the henselization gives the same ideal. -/
@[stacks 07QM "maximal ideals in a henselization-strict-henselization tower"]
theorem map_baseMaximalIdeal_eq_map_henselizationMaximalIdeal :
    Ideal.map (algebraMap R S) (maximalIdeal R) =
      Ideal.map (algebraMap Rh S) (maximalIdeal Rh) := sorry

end Tower

end IsStrictHenselizationOf
