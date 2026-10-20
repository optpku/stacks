module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.WeaklyUnramifiedBaseChange
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.TotalRamification
public import ReasLib.RingTheory.Normal.Nagata
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Purely inseparable ramification elimination

The source statement for Lemma 15.116.9 mentions the two field tensor products and the adjacent
maps of their integral closures explicitly.  `SourceTower` keeps those exact carriers, their DVR
structures, and both canonical weakly unramified maps visible at the API boundary.

@stack 09EY
-/

open scoped TensorProduct
open Ideal IsLocalRing
open IsExtensionOfDiscreteValuationRings
open DVR.Field

universe u v w x y z t

namespace IsWeakSolutionFor

section Elimination

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [NagataRing B]
variable [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [IsExtensionOfDiscreteValuationRings A B]
variable [IsExtensionOfDiscreteValuationRings B C]
variable {K : Type x} {L : Type y} {M : Type z}
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsFractionRing B L] [IsScalarTower A B L] [IsScalarTower A K L]
variable [Field M] [Algebra A M] [Algebra B M] [Algebra C M] [Algebra K M] [Algebra L M]
variable [IsFractionRing C M] [IsScalarTower A B M] [IsScalarTower A C M]
variable [IsScalarTower A K M] [IsScalarTower B C M] [IsScalarTower B L M]
variable [IsScalarTower K L M]
variable {p : ℕ} [Fact p.Prime] [CharP K p]

/-- Lemma 15.116.9: a degree-`p` purely inseparable step can be eliminated by a weakly
unramified composite, a `p`th-root extension of a uniformizer, or a separable totally ramified
extension carrying the source tensor-field view.  The composite DVR extension is derived from the
two adjacent extension instances; the companion with an explicit composite instance is provided
below for consumers that already have it.
-/
@[stacks 09EY "purely inseparable ramification elimination"]
theorem ramificationElimination
    [FiniteDimensional L M] [IsPurelyInseparable L M]
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    (hAB : WeaklyUnramified A B) (hLM : Module.finrank L M = p) :
    -- Local instance justification (proof-local temporary data): derive the composite DVR
    -- extension from the adjacent tower only for this source-facing statement.
    let _ : IsExtensionOfDiscreteValuationRings A C := of_tower A B C
    WeaklyUnramified A C ∨
      (∃ x : C, x ^ p = algebraMap A C π ∧ Algebra.adjoin B ({x} : Set C) = ⊤) ∨
      ∃ (K1 : Type (max u v w x y z)) (_ : Field K1) (_ : Algebra A K1)
        (_ : Algebra K K1) (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1)
        (_ : Algebra.IsSeparable K K1),
        IsTotallyRamified A K K1 ∧ Module.finrank K K1 = p ∧
          DVR.BaseChange.SourceTower A B C K L M K1 := sorry
-- Proof strategy: compare the chosen fraction fields `L ⊆ M` with the canonical fraction rings
-- of `B ⊆ C` and use pure inseparability plus `hLM` to show that the ramification index of
-- `B ⊆ C` is `1` or `p`.  In the first case, multiply ramification indices in the tower and use
-- `hAB`.  In the second case, choose a uniformizer of `C`, write its `p`th power as a unit times
-- `π`, and split at the first coefficient that is not a residue `p`th power.  The power branch
-- gives the displayed generator; the other branch combines the prescribed extension from 09EW,
-- the Kummer normalization from 09EX, and the weakly-unramified base-change API to construct the
-- stated `SourceTower`.

/-- Lemma 15.116.9 with an explicit composite DVR extension. -/
@[stacks 09EY "purely inseparable ramification elimination with composite extension"]
theorem ramificationElimination_of_extension
    [IsExtensionOfDiscreteValuationRings A C]
    [FiniteDimensional L M] [IsPurelyInseparable L M]
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A))
    (hAB : WeaklyUnramified A B) (hLM : Module.finrank L M = p) :
    WeaklyUnramified A C ∨
      (∃ x : C, x ^ p = algebraMap A C π ∧ Algebra.adjoin B ({x} : Set C) = ⊤) ∨
      ∃ (K1 : Type (max u v w x y z)) (_ : Field K1) (_ : Algebra A K1)
        (_ : Algebra K K1) (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1)
        (_ : Algebra.IsSeparable K K1),
        IsTotallyRamified A K K1 ∧ Module.finrank K K1 = p ∧
          DVR.BaseChange.SourceTower A B C K L M K1 := sorry
-- Proof strategy: apply `ramificationElimination` and identify the existing composite
-- `IsExtensionOfDiscreteValuationRings A C` instance with `of_tower A B C` by proof irrelevance;
-- all three alternatives and the `SourceTower` data are otherwise unchanged.

end Elimination

end IsWeakSolutionFor

end
