/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.PurelyInseparableStep
public import ReasLib.RingTheory.Normal.Nagata.EssentialFiniteness
import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange.FiniteType
import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.Epp
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Solutions for essentially finite-type extensions of DVRs

This module owns the existence statements for solutions of an essentially finite-type extension
of discrete valuation rings. The source-facing Nagata disjunction remains explicit, while a
separate specialization exposes the common downstream case in which the target is already known
to be Nagata. The input fraction-field extension may be transcendental; only the finite output
extension is required to be algebraic separable.

@stack 09II
@stack 0BRP
-/

universe u v w x

namespace IsSolutionFor

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Algebra.EssFiniteType A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

/-- Proposition 15.117.8: an essentially finite-type extension of discrete valuation rings has a
finite extension of the base fraction field that is a solution. -/
@[stacks 09II "Proposition 15.117.8: existence of a solution for an essentially finite-type DVR extension"]
theorem exists_of_essFiniteType :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsSolutionFor A B K L K1 := sorry
-- Proof strategy: split on `ringChar (ResidueField A)`.  In residue characteristic zero, the Epp
-- hypothesis is vacuous; apply `IsWeakSolutionFor.exists_of_epp`, note that every algebraic branch
-- residue extension over the resulting perfect source residue field is separable, and upgrade the
-- weak solution to `IsSolutionFor` branchwise.  In positive characteristic, choose a p-basis of
-- `ResidueField A` and lifts in `A`, adjoin compatible successive p-power roots inside an algebraic
-- closure, and apply Epp over the resulting perfected DVR base.  Use
-- `DVR.BaseChange.targetNormalization_noetherian`, spectrum surjectivity, and
-- `DVR.BaseChange.residueField_finiteType` to descend formal smoothness and all branch data to one
-- finite stage of the root tower, yielding the required finite solution over `K`.

/-- Lemma 15.117.9: if either endpoint of an essentially finite-type DVR extension is Nagata and
the fraction-field extension is separable, then the extension has a separable solution. -/
@[stacks 0BRP "Lemma 15.117.9: existence of a separable solution under the Nagata hypothesis"]
theorem exists_separable_of_essFiniteType
    (hNagata : NagataRing A ∨ NagataRing B)
    (hsepKL : Algebra.IsSeparableOver K L) :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsSeparableSolutionFor A B K L K1 := sorry
-- Proof strategy: obtain `NagataRing B`: use `NagataRing.of_essFiniteType` in the left disjunct of
-- `hNagata`, and the supplied instance in the right disjunct.  Apply `exists_of_essFiniteType` to
-- get a finite solution and then `IsSolutionFor.exists_separable_of_exists hsepKL` to replace it by
-- a solution separable over `K`, preserving the requested universe and tower witnesses.

/-- The target-Nagata specialization of separable-solution existence for an essentially
finite-type extension of discrete valuation rings. -/
@[stacks 0BRP "Target-Nagata specialization of Lemma 15.117.9"]
theorem exists_separable_of_essFiniteType_of_target [NagataRing B]
    (hsepKL : Algebra.IsSeparableOver K L) :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsSeparableSolutionFor A B K L K1 := sorry
-- Proof strategy: apply `exists_separable_of_essFiniteType` with `Or.inr` and the ambient
-- `NagataRing B` instance; no additional field or tower construction is required.

end

end IsSolutionFor

end
