/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.GeometricRegularity.Local
public import ReasLib.RingTheory.Smooth.Adic.Regularity
import Mathlib.Tactic.CrossRefAttribute

/-!
# Geometric Regularity and Adic Formal Smoothness

@stack 07EL
-/

@[expose] public section

noncomputable section

open Algebra IsLocalRing IntermediateField
open scoped TensorProduct

universe u v

/-- Theorem 15.40.1 (1) (07EL): over a characteristic-zero field, a Noetherian local algebra is
regular exactly when its structure map is formally smooth for the maximal-ideal-adic topology. -/
@[stacks 07EL "part 1, characteristic zero"]
theorem regularLocalRing_iff_formallySmooth_for_maximalIdeal_adic_of_charZero
    {k : Type u} {A : Type v} [Field k] [CharZero k]
    [CommRing A] [Algebra k A] [IsLocalRing A] [IsNoetherianRing A] :
    IsRegularLocalRing A ↔
      (algebraMap k A).formally_smooth_for_adic (maximalIdeal A) := sorry

/-- Theorem 15.40.1 (2) (07EL): in positive characteristic, geometric regularity, maximal-adic
formal smoothness, regularity after every finite subextension of `k^(1/p)`, and the two canonical
cotangent injectivity criteria are equivalent. -/
@[stacks 07EL "part 2, positive characteristic"]
theorem geometricallyRegular_formallySmooth_for_maximalIdeal_adic_tfae_of_charP
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A] (p : ℕ) [Fact p.Prime] [CharP k p] :
    -- Local instance justification (proof-local temporary data): the field-algebra map transfers
    -- the source characteristic canonically to `A` for this criterion.
    letI : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
    -- Local instance justification (instance diamond): choose the canonical prime-field action on
    -- `k` only while forming the differential comparison map.
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    -- Local instance justification (instance diamond): choose the matching prime-field action on
    -- `A` only inside this criterion.
    letI : Algebra (ZMod p) A := ZMod.algebra A p
    -- Local instance justification (defeq pin): align the two prime-field actions with the given
    -- `k`-algebra structure on `A`.
    letI : IsScalarTower (ZMod p) k A := inferInstance
    List.TFAE [
      IsGeometricallyRegular k A,
      (algebraMap k A).formally_smooth_for_adic (maximalIdeal A),
      ∀ (K : IntermediateField k (AlgebraicClosure k)) [FiniteDimensional k K],
        K ≤ onePthRootExtension k p → IsRegularRing (K ⊗[k] A),
      IsRegularLocalRing A ∧
        Function.Injective (H1Cotangent.map k A (ResidueField A) (ResidueField A)),
      IsRegularLocalRing A ∧
        Function.Injective (KaehlerDifferential.residueFieldComparison (ZMod p) k A)
    ] := sorry
