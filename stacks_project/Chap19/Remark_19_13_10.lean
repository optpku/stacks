/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence
import StacksCheckRecall

@[expose] public section

/-!
# The Source-Filtered Ext Spectral Sequence

This is the contravariant companion to the target-filtered construction.  Its stabilization
hypothesis uses the canonical map from the underlying complex to `M / F^p M`, and the resulting
spectral sequence is associated to an actual filtered Hom complex.
-/

open CategoryTheory

noncomputable section

universe t w v u

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{t} A] [IsGrothendieckAbelian.{w} A]

/- Remark 19.13.10: the source filtration gives an associated Ext spectral sequence with the
stated first page, boundedness criterion, and convergence to total Ext. -/
@[stacks 0G1Z] #check
  fun (M : FilteredComplex A) (K : DerivedCategory A) ↦
    (DerivedCategory.Ext.Source.existsSpectralSequence M K :
      ∃ (F : FilteredComplex AddCommGrpCat.{t})
        (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0),
        DerivedCategory.Ext.Source.IsSpectralSequence M K F E)

/- The boundedness hypotheses are expressed through canonical Ext maps from the quotient
complexes. -/
#check @DerivedCategory.Ext.Source.VanishesBelow
#check @DerivedCategory.Ext.Source.StabilizesAbove
