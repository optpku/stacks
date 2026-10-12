/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ramification-elimination squares

This leaf owns the square of DVR extensions used to reduce weak, formal-smooth, and separable
solutions to extensions with separably closed residue fields.

@stack 09ET
-/

@[expose] public section

open IsLocalRing

universe u v w x uA vA wA xA

namespace DVR.RamificationElimination

section

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

set_option linter.checkUnivs false in
/-- The chosen rings, fields, comparison maps, and descent properties in the
ramification-elimination square of Lemma 15.116.5 (09ET).

The instance-valued projections are not registered globally: two chosen squares over the same
base need not use definitionally equal models, so consumers install the projections of one square
only in the local proof where it is used. -/
@[stacks 09ET "ramification-elimination square data"]
structure Square where
  /-- The upper-left discrete valuation ring. -/
  Aprime : Type uA
  [commRingAprime : CommRing Aprime]
  [isDomainAprime : IsDomain Aprime]
  [isDVRAprime : IsDiscreteValuationRing Aprime]
  [algebraAAprime : Algebra A Aprime]
  [extensionAAprime : IsExtensionOfDiscreteValuationRings A Aprime]
  /-- The upper-right discrete valuation ring. -/
  Bprime : Type vA
  [commRingBprime : CommRing Bprime]
  [isDomainBprime : IsDomain Bprime]
  [isDVRBprime : IsDiscreteValuationRing Bprime]
  [algebraBBprime : Algebra B Bprime]
  [algebraAprimeBprime : Algebra Aprime Bprime]
  [algebraABprime : Algebra A Bprime]
  [towerAAprimeBprime : IsScalarTower A Aprime Bprime]
  [towerABBprime : IsScalarTower A B Bprime]
  [extensionBBprime : IsExtensionOfDiscreteValuationRings B Bprime]
  [extensionAprimeBprime : IsExtensionOfDiscreteValuationRings Aprime Bprime]
  /-- The chosen fraction field of `Aprime`, compatible with `K`. -/
  Kprime : Type wA
  [fieldKprime : Field Kprime]
  [algebraAprimeKprime : Algebra Aprime Kprime]
  [fractionRingAprimeKprime : IsFractionRing Aprime Kprime]
  [algebraKKprime : Algebra K Kprime]
  [algebraAKprime : Algebra A Kprime]
  [towerAAprimeKprime : IsScalarTower A Aprime Kprime]
  [towerAKKprime : IsScalarTower A K Kprime]
  /-- The chosen fraction field of `Bprime`, compatible with `L` and `Kprime`. -/
  Lprime : Type xA
  [fieldLprime : Field Lprime]
  [algebraBprimeLprime : Algebra Bprime Lprime]
  [fractionRingBprimeLprime : IsFractionRing Bprime Lprime]
  [algebraLLprime : Algebra L Lprime]
  [algebraBLprime : Algebra B Lprime]
  [towerBBprimeLprime : IsScalarTower B Bprime Lprime]
  [towerBLLprime : IsScalarTower B L Lprime]
  [algebraKprimeLprime : Algebra Kprime Lprime]
  [algebraAprimeLprime : Algebra Aprime Lprime]
  [towerAprimeBprimeLprime : IsScalarTower Aprime Bprime Lprime]
  [towerAprimeKprimeLprime : IsScalarTower Aprime Kprime Lprime]
  /-- The residue-field maps making the lower and upper squares compatible. -/
  [residueAlgebraAAprime : Algebra (ResidueField A) (ResidueField Aprime)]
  [residueAlgebraBBprime : Algebra (ResidueField B) (ResidueField Bprime)]
  [residueAlgebraAprimeBprime : Algebra (ResidueField Aprime) (ResidueField Bprime)]
  [residueAlgebraABprime : Algebra (ResidueField A) (ResidueField Bprime)]
  [residueTowerAAprimeBprime :
    IsScalarTower (ResidueField A) (ResidueField Aprime) (ResidueField Bprime)]
  [residueTowerABBprime :
    IsScalarTower (ResidueField A) (ResidueField B) (ResidueField Bprime)]
  /-- The new left fraction field is algebraic over the old one. -/
  algebraicKprime : Algebra.IsAlgebraic K Kprime
  /-- The new left fraction field is separable over the old one. -/
  separableKprime : Algebra.IsSeparable K Kprime
  /-- The new right fraction field is algebraic over the old one. -/
  algebraicLprime : Algebra.IsAlgebraic L Lprime
  /-- The new right fraction field is separable over the old one. -/
  separableLprime : Algebra.IsSeparable L Lprime
  /-- The upper-left residue field is a separable closure of the lower-left residue field. -/
  residueAprimeIsSepClosure : IsSepClosure (ResidueField A) (ResidueField Aprime)
  /-- The upper-right residue field is a separable closure of the lower-right residue field. -/
  residueBprimeIsSepClosure : IsSepClosure (ResidueField B) (ResidueField Bprime)
  /-- A weak solution for the upper square descends to the original extension. -/
  weakSolutionDescent :
    (∃ (K1prime : Type (max uA vA wA xA)) (_ : Field K1prime)
        (_ : Algebra Aprime K1prime) (_ : Algebra Kprime K1prime)
        (_ : IsScalarTower Aprime Kprime K1prime)
        (_ : FiniteDimensional Kprime K1prime),
        IsWeakSolutionFor Aprime Bprime Kprime Lprime K1prime) →
      ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1)
        (_ : Algebra K K1) (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
        IsWeakSolutionFor A B K L K1
  /-- A formal-smooth solution for the upper square descends to the original extension. -/
  solutionDescent :
    (∃ (K1prime : Type (max uA vA wA xA)) (_ : Field K1prime)
        (_ : Algebra Aprime K1prime) (_ : Algebra Kprime K1prime)
        (_ : IsScalarTower Aprime Kprime K1prime)
        (_ : FiniteDimensional Kprime K1prime),
        IsSolutionFor Aprime Bprime Kprime Lprime K1prime) →
      ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1)
        (_ : Algebra K K1) (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
        IsSolutionFor A B K L K1
  /-- A separable solution for the upper square descends to the original extension. -/
  separableSolutionDescent :
    (∃ (K1prime : Type (max uA vA wA xA)) (_ : Field K1prime)
        (_ : Algebra Aprime K1prime) (_ : Algebra Kprime K1prime)
        (_ : IsScalarTower Aprime Kprime K1prime)
        (_ : FiniteDimensional Kprime K1prime),
        IsSeparableSolutionFor Aprime Bprime Kprime Lprime K1prime) →
      ∃ (K1 : Type (max u v w x)) (_ : Field K1) (_ : Algebra A K1)
        (_ : Algebra K K1) (_ : IsScalarTower A K K1) (_ : FiniteDimensional K K1),
        IsSeparableSolutionFor A B K L K1

/-- Lemma 15.116.5 (09ET): every DVR extension admits a ramification-elimination square whose
fraction-field extensions are separable algebraic, whose residue fields are separable closures,
and along which weak, formal-smooth, and separable solutions descend. -/
@[stacks 09ET "Lemma 15.116.5: ramification-elimination square"]
theorem exists_square : Nonempty (Square (A := A) (B := B) (K := K) (L := L)) := sorry
-- Proof strategy: choose compatible strict henselizations of `A` and `B` by lifting the residue
-- field map through canonical separable closures; identify their fraction fields through the
-- zero-prime residue fields to obtain the algebraic and separable generic extensions.  Prove the
-- three descent fields by approximating a finite solution over the strict henselization at one
-- finite etale local stage and applying the 09ES composition/descent theorems.

end

end DVR.RamificationElimination
