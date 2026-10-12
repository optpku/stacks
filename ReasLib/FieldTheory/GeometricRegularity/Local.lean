/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Algebra.Algebra.ZMod
public import ReasLib.FieldTheory.GeometricRegularity
public import ReasLib.FieldTheory.PurelyInseparable.OnePthRoot
public import ReasLib.RingTheory.LocalRing.ResidueField.Cotangent.BaseChange
public import ReasLib.RingTheory.LocalRing.ResidueField.Cotangent.JacobiZariski
public import ReasLib.RingTheory.RegularLocalRing.SerreCondition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Geometric regularity criteria for local algebras

This leaf owns the positive-characteristic local criterion relating geometric
regularity, finite purely inseparable tests, first cotangent homology, and
Kaehler differentials over the prime field.

@stack 07E5
-/

@[expose] public section

open IsLocalRing IntermediateField
open scoped TensorProduct

noncomputable section

universe u v

namespace Algebra

/-- Proposition 15.35.1, tag `07E5`: for a
Noetherian local `k`-algebra in positive characteristic, geometric regularity,
the finite subextensions of `k^(1/p)`, and the two cotangent injectivity
criteria are equivalent. The third clause uses the underlying `H1Cotangent`
map; `Algebra.H1Cotangent.ResidueField.toCotangent_injective_iff` identifies it
with the source map to `maximalIdeal A / maximalIdeal A ^ 2`. -/
@[stacks 07E5 "geometric regularity criteria"]
theorem geometricallyRegularLocalRing_tfae_of_charP
    {k : Type u} {A : Type v} [Field k] [CommRing A] [IsLocalRing A]
    [Algebra k A] {p : ℕ} [Fact p.Prime] [CharP k p] [IsNoetherianRing A] :
    -- Local instance justification (proof-local temporary data): the target characteristic is
    -- canonically induced through the injective field-algebra map.
    letI : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
    -- Local instance justification (instance diamond): Mathlib keeps the prime-field algebra on
    -- `k` explicit because several algebra structures can coexist.
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    -- Local instance justification (instance diamond): use the matching prime-field action on
    -- `A` only while forming the fourth source clause.
    letI : Algebra (ZMod p) A := ZMod.algebra A p
    -- Local instance justification (defeq pin): align the two explicit prime-field actions with
    -- the given `k`-algebra structure on `A`.
    letI : IsScalarTower (ZMod p) k A := inferInstance
    List.TFAE [
      IsGeometricallyRegular k A,
      ∀ (K : IntermediateField k (AlgebraicClosure k)) [FiniteDimensional k K],
        K ≤ onePthRootExtension k p → IsRegularRing (K ⊗[k] A),
      IsRegularLocalRing A ∧
        Function.Injective (H1Cotangent.map k A (ResidueField A) (ResidueField A)),
      IsRegularLocalRing A ∧
        Function.Injective (KaehlerDifferential.residueFieldComparison (ZMod p) k A)
    ] := sorry

end Algebra
