/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution
public import ReasLib.FieldTheory.PurelyInseparable.FiniteTower
public import ReasLib.FieldTheory.Separable.Generated.Properties
public import ReasLib.RingTheory.Normal.Nagata
import ReasLib.RingTheory.Localization.Away.FiniteExtension.PrincipalQuotient
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Separable replacement of a prime purely inseparable solution step

This module owns the reusable existence contract behind Lemma 15.117.5.  The source theorem is
kept at the `IsSolutionFor` layer: the purely inseparable step, its prime finite dimension, the
Nagata hypothesis, and separability of the original fraction-field extension remain explicit in
the declaration, while the chapter file only provides a traceable recall.

@stack 0GLV
@stack 0BRN
-/

universe u v w x y z

namespace IsSolutionFor

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y} {K2 : Type z}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field K1] [Algebra K K1] [Algebra A K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]
variable [Field K2] [Algebra K1 K2] [Algebra K K2] [Algebra A K2]
variable [IsScalarTower K K1 K2] [IsScalarTower A K K2] [IsScalarTower A K1 K2]
variable [FiniteDimensional K1 K2] [FiniteDimensional K K2]
variable {p : ℕ} [Fact p.Prime] [CharP K p]
variable [Algebra.IsSeparableOver K L] [NagataRing B] [IsPurelyInseparable K1 K2]

/-- Lemma 15.117.5: a solution over a prime purely inseparable finite step can be replaced by a
finite extension separable over the intermediate field while preserving the solution predicate.
The carrier, all scalar actions, the two finite-dimensionality hypotheses, the Nagata condition,
and the purely inseparable/separable assumptions are part of the source-faithful contract.  The
derived `K / K₃` finite-dimensional witness is explicit because `IsSolutionFor` consumes it as a
typeclass and tower transitivity is not a global instance. -/
@[stacks 0GLV "Lemma 15.117.5: separable replacement of a prime purely inseparable solution"]
theorem exists_separable_of_purelyInseparable_prime
    (hK2 : IsSolutionFor A B K L K2)
    (hdeg : Module.finrank K1 K2 = p) :
    ∃ (K3 : Type (max u v w x y z)) (_ : Field K3) (_ : Algebra A K3) (_ : Algebra K K3)
      (_ : IsScalarTower A K K3) (_ : Algebra K1 K3) (_ : IsScalarTower K K1 K3)
      (_ : FiniteDimensional K K3) (_ : FiniteDimensional K1 K3)
      (_ : Algebra.IsSeparable K1 K3),
      IsSolutionFor A B K L K3 := sorry
-- Proof strategy: choose a generator `beta` of the prime-degree purely inseparable extension with
-- `beta ^ p` in `integralClosure A K1`, after rescaling by a source denominator.  Present the
-- source and target normalizations by the corresponding monogenic `X ^ p - a` algebras.  Nagata
-- descent makes the source normalization finite, while separability of `L / K` controls the target
-- reduced tensor branch.  Apply the functorial principal-power quotient lifting theorem 0GLU to
-- the two away-isomorphisms, then deform the inseparable polynomial by the chosen uniformizer to a
-- separable polynomial.  Its finite field factor defines `K3`; the quotient squares identify the
-- localized branches deeply enough for the adic formal-smoothness criterion to transport `hK2`
-- to `K3`.  Finally assemble the algebra towers and finite-dimensional witnesses.

omit [Algebra.IsSeparableOver K L] in
/-- Lemma 15.117.6: for a Nagata extension of DVRs with separable fraction fields, any finite
solution can be replaced by one that is separable over the base fraction field. -/
@[stacks 0BRN "Lemma 15.117.6: separable refinement of a solution"]
theorem exists_separable_of_exists
    (hsepKL : Algebra.IsSeparableOver K L)
    (hsol :
      ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
        (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
        IsSolutionFor A B K L K1) :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsSeparableSolutionFor A B K L K1 := sorry
-- Proof strategy: unpack `hsol` and induct on `Field.insepDegree K K1`.  If the inseparable degree
-- is one, the chosen solution is already separable.  Otherwise use the finite purely inseparable
-- tower API to factor through an intermediate field whose last step has prime purely inseparable
-- degree.  Apply `exists_separable_of_purelyInseparable_prime` to replace that last step by a
-- separable solution, use finite-extension stability to align the resulting towers, and invoke
-- multiplicativity of inseparable degree to obtain a strictly smaller induction parameter.

end

end IsSolutionFor

end
