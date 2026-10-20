/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Ext.SpectralSequence
import StacksCheckRecall

@[expose] public section

/-!
# The Target-Filtered Ext Spectral Sequence

The chapter entry is a direct bridge to the reusable target-filtration model.  In particular,
the Ext groups use the global `Ext⁽n⁾(X, Y)` notation and the spectral sequence is tied to an
actual filtered complex by `FilteredComplex.IsAssociated`.
-/

open CategoryTheory

noncomputable section

universe t w v u

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{t} A] [IsGrothendieckAbelian.{w} A]

/- Remark 19.13.8: the target filtration gives an associated Ext spectral sequence with the
stated first page, boundedness criterion, and convergence to total Ext. -/
@[stacks 0G1X] #check
  fun (M : DerivedCategory A) (K : FilteredComplex A) ↦
    (DerivedCategory.Ext.Target.existsSpectralSequence M K :
      ∃ (F : FilteredComplex AddCommGrpCat.{t})
        (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0),
        DerivedCategory.Ext.Target.IsSpectralSequence M K F E)

/- The boundedness hypotheses are expressed through the canonical Ext maps induced by the
filtration inclusions. -/
#check @DerivedCategory.Ext.Target.VanishesAbove
#check @DerivedCategory.Ext.Target.StabilizesBelow
