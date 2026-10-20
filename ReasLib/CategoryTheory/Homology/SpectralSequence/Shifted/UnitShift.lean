module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import ReasLib.CategoryTheory.Homology.ShiftedDifferentialObject.Iteration
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Shifted
public import ReasLib.Data.PNat.Int

/-!
# Unit-Shifted Spectral Sequences

This module unfolds a shifted spectral sequence with constant translation `X ↦ X⟦1⟧` into a
mathlib spectral sequence of cochain complexes indexed by all integral shifts.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasShift A ℤ]

namespace ShiftedSpectralSequence

open ShiftedDifferentialObject
open ShiftedDifferentialObject.Iteration

variable (S : ShiftedSpectralSequence
  (fun _ : ℕ+ ↦ (shiftFunctor A (1 : ℤ)).asEquivalence))

/-- The homology comparison used by the unit-shift bridge on consecutive pages. -/
@[stacks 0AMI "unit-shift consecutive-page comparison"]
noncomputable def toSpectralSequenceIso (r r' n : ℤ) (hrr' : r + 1 = r')
    (hr : 1 ≤ r) :
    (complex (S.page (PNat.ofInt r hr))).homology n ≅
      (complex
        (S.page (PNat.ofInt r'
          (hrr' ▸ hr.trans
            (le_add_of_nonneg_right (Int.natCast_nonneg 1)))))).X n :=
  homologyIso (S.page (PNat.ofInt r hr)) n ≪≫
    (shiftFunctor A n).mapIso (S.iso (PNat.ofInt r hr)) ≪≫
      eqToIso
        (congrArg (fun q : ℕ+ ↦ (S.page q).obj⟦n⟧)
          (hrr'.rec
            (@PNat.eq
              (PNat.ofInt (r + 1)
                (hr.trans
                  (le_add_of_nonneg_right (Int.natCast_nonneg 1))))
              (PNat.ofInt r hr + 1)
              (Int.toNat_add
                (Int.le_of_lt (lt_of_lt_of_le Int.zero_lt_one hr))
                (Int.natCast_nonneg 1))).symm))

/-- A spectral sequence with the constant unit shift canonically determines a mathlib spectral
sequence whose page complexes consist of all integral shifts of the page object. -/
@[stacks 0AMI "unit-shift specialization"]
noncomputable def toSpectralSequence :
    SpectralSequence A (fun _ : ℤ ↦ ComplexShape.up ℤ) 1 where
  page r hr := complex (S.page (PNat.ofInt r hr))
  iso r r' n hrr' hr := S.toSpectralSequenceIso r r' n hrr' hr

/-- The degree-zero component of the bridged page complex is the original shifted page object. -/
@[stacks 0AMI "degree-zero unit-shift comparison"]
noncomputable def pageZeroIso (r : ℕ+) :
    ((S.toSpectralSequence.page (r : ℤ)
      (Int.ofNat_le.mpr (Nat.succ_le_iff.mpr r.pos))).X (0 : ℤ)) ≅
      (S.page r).obj :=
  shiftZero ℤ (S.page r).obj

end ShiftedSpectralSequence

end CategoryTheory
