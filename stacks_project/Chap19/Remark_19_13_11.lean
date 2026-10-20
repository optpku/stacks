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
# Source Hyper-Ext Spectral Sequences

The source truncation, its representation-independent renumbering, and the source stupid
filtration are exposed as three fine-grained models sharing the same association and convergence
infrastructure.
-/

open CategoryTheory

noncomputable section

universe t w v u

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{t} A] [IsGrothendieckAbelian.{w} A]

/- Remark 19.13.11 (1): the source truncation filtration has
`E₁^{p,q} = Ext⁽2p+q⁾(H^p(M), K)`. -/
@[stacks 0G20 "source truncation filtration"] #check
  fun (M K : DerivedCategory A) ↦
    (DerivedCategory.Ext.Source.Truncation.existsSpectralSequence M K :
      ∃ (F : FilteredComplex AddCommGrpCat.{t})
        (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0),
        DerivedCategory.Ext.Source.Truncation.IsSpectralSequence M K F E)

/- Remark 19.13.11 (2): after renumbering,
`E'_r^{i,j} = E_{r-1}^{-j,i+2j}` for `r ≥ 2`, and
`E'_2^{i,j} = Ext⁽i⁾(H^{-j}(M), K)`. -/
@[stacks 0G20 "renumbered source cohomology spectral sequence"] #check
  fun (M K : DerivedCategory A) ↦
    (DerivedCategory.Ext.Source.Cohomology.existsSpectralSequence M K :
      ∃ (F : FilteredComplex AddCommGrpCat.{t})
        (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0)
        (E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{t}),
        DerivedCategory.Ext.Source.Cohomology.IsSpectralSequence M K F E E')

/- Remark 19.13.11 (3): the source stupid filtration has
`E₁^{p,q} = Ext⁽q⁾(M^{-p}, K)`. -/
@[stacks 0G20 "source stupid filtration"] #check
  fun (M : CochainComplex A ℤ) (K : DerivedCategory A) ↦
    (DerivedCategory.Ext.Source.Stupid.existsSpectralSequence M K :
      ∃ (F : FilteredComplex AddCommGrpCat.{t})
        (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0),
        DerivedCategory.Ext.Source.Stupid.IsSpectralSequence M K F E)
