module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.FieldTheory.PurelyInseparable.PowerIntersection
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import ReasLib.FieldTheory.Kummer.FiniteLevel.EliminateRamification
import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.ArtinSchreier
import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.Composition
import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.PurelyInseparable
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Complete-residue-field existence for weak solutions

This module owns the reusable existence statement behind Lemma 15.116.17.  The proof is deliberately
separate from the branch predicate: later consumers can import the statement and its hypotheses
without importing a chapter file.

@stack 09F8
-/

open IsLocalRing
open IsExtensionOfDiscreteValuationRings

universe u v w x y z

namespace IsWeakSolutionFor

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsCompleteLocalRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [IsCompleteLocalRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable {K : Type x} {L : Type y} {M : Type z}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field M] [Algebra C M] [IsFractionRing C M] [Algebra K M]
variable [Algebra A M] [IsScalarTower A C M] [IsScalarTower A K M]
variable {p : ℕ} [Fact p.Prime] [CharP (ResidueField A) p] [IsAlgClosed (ResidueField A)]

/-- Lemma 15.116.17 (09F8): over complete DVRs with algebraically closed residue field, a
weakly-unramified intermediate extension and the stable p-power intersection condition yield a
finite weak solution for the composite extension. -/
@[stacks 09F8 "Lemma 15.116.17: complete weak-solution existence"]
theorem exists_of_complete
    [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    [Algebra L M] [IsScalarTower K L M] [FiniteDimensional L M]
    (hAB : WeaklyUnramified A B)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        PerfectClosure.powerIntersection (ResidueField B) p) :
    -- Local instance justification (proof-local temporary data): the tower supplies the
    -- canonical composite DVR extension only for the conclusion of this source theorem.
    let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
    ∃ (K1 : Type (max u v w x y z)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsWeakSolutionFor A C K M K1 := sorry
-- Proof strategy: replace the finite extension `M / L` by a finite normal closure and localize
-- the normalization of `C` at a maximal branch above its maximal ideal.  Refine the resulting
-- normal extension into prime purely inseparable, tame cyclic, and degree-`p` Galois steps.  Induct
-- along that tower, using `IsWeakSolutionFor.ramificationElimination` for purely inseparable steps,
-- `IsWeakSolutionFor.exists_of_degree_p_galois` in equal characteristic, and the 09F4/09F5
-- `FiniteLevel.BaseChange.exists_totallyRamified` and
-- `FiniteLevel.Descent.exists_totallyRamified` alternatives in mixed characteristic.  In the
-- descent branch the bound `max 0 (max (l - 1) (2 * l - p))` strictly lowers every positive exact
-- level, so iteration terminates.  Transport `hκ` through the weakly-unramified intermediate
-- rings, use algebraic closedness of `ResidueField A` for the tame and unramified branches, compose
-- the resulting weak solutions with the shared composition API, descend from the chosen normal-
-- closure branch to `C`, and package the composite finite field extension as `K1`.

/-- A downstream-friendly form of `exists_of_complete` when the composite DVR extension is already
available as a canonical instance.  This companion keeps the conclusion free of a hidden
statement-level `let` while retaining the source theorem above for the tower-specialized entry. -/
@[stacks 09F8 "Lemma 15.116.17: explicit composite-extension view"]
theorem exists_of_complete_of_extension
    [IsExtensionOfDiscreteValuationRings A C]
    [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
    [Algebra L M] [IsScalarTower K L M] [FiniteDimensional L M]
    (hAB : WeaklyUnramified A B)
    (hκ :
      (Set.range (algebraMap (ResidueField A) (ResidueField B)) : Set (ResidueField B)) =
        PerfectClosure.powerIntersection (ResidueField B) p) :
    ∃ (K1 : Type (max u v w x y z)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsWeakSolutionFor A C K M K1 := sorry
-- Proof strategy: apply `exists_of_complete` with the tower-derived instance `of_tower A B C`;
-- identify that proposition-valued instance with the supplied composite DVR-extension instance by
-- proof irrelevance, and retain the same finite field, algebra, scalar-tower, and weak-solution
-- witnesses.

end

end IsWeakSolutionFor
