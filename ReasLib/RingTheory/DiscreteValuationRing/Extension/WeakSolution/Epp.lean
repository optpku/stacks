module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution
public import ReasLib.FieldTheory.PurelyInseparable.PowerIntersection
import ReasLib.RingTheory.Completion.CohenStructure
import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange.Abhyankar
import ReasLib.RingTheory.DiscreteValuationRing.Extension.UniformizerRoot
import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.Complete
import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.RamificationElimination
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Epp existence for weak solutions

This module owns the residue-field hypothesis and the finite weak-solution conclusion of Epp's
theorem. The source theorem in Chapter 15 is only a tagged check of this owner.

@stack 09F9
-/

open IsLocalRing

universe u v w x

namespace IsWeakSolutionFor

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

/-- Theorem 15.116.18 (09F9, Epp): if every stable p-power residue element is separable over the
source residue field in positive residue characteristic, then a finite weak solution exists. -/
@[stacks 09F9 "Theorem 15.116.18: Epp weak-solution existence"]
theorem exists_of_epp
    (hsep :
      ringChar (ResidueField A) ≠ 0 →
        ∀ x : ResidueField B,
          x ∈ PerfectClosure.powerIntersection (ResidueField B) (ringChar (ResidueField A)) →
            IsSeparable (ResidueField A) x) :
    ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1) (_ : Algebra K K1)
      (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
      IsWeakSolutionFor A B K L K1 := sorry
-- Proof strategy: split on `ringChar (ResidueField A)`.  In characteristic zero, put
-- `e = ramificationIndex A B`, choose a uniformizer `π` of `A`, and use the explicit
-- `DVR.UniformizerRoot.RootExtension π e`; the residue extension is separable and `e` is prime to
-- the residue characteristic, so `DVR.Field.BaseChange.formallySmoothAtOfTameAndDvd` makes every
-- normalized tensor branch weakly unramified and yields the required weak solution.  In positive
-- characteristic, choose `DVR.RamificationElimination.exists_square` and locally install the
-- square's ring, field, tower, and residue-field projections.  Use `hsep`, separable-closure
-- transport, and the Frobenius/minimal-polynomial argument to identify the upper-right stable
-- power intersection with the image of a perfect subfield of the upper-left residue field.
-- Apply the coefficient/Cohen and completion API to replace the upper square by complete DVRs
-- whose left residue field is algebraically closed and whose residue image is exactly that stable
-- intersection.  Invoke `IsWeakSolutionFor.exists_of_complete` on this complete square and finish
-- with `DVR.RamificationElimination.Square.weakSolutionDescent`.

end

end IsWeakSolutionFor
