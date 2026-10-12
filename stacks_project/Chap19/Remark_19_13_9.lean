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
# Hyper-Ext Spectral Sequences

The three source formulations are kept as separate reusable models: the unrenumbered truncation
sequence, its representation-independent `E₂` form, and the stupid-filtration sequence.  Each is
associated to a genuine filtered complex and carries an actual convergence predicate.
-/

open CategoryTheory

noncomputable section

universe t w v u

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{t} A] [IsGrothendieckAbelian.{w} A]

/- Remark 19.13.9 (1): the truncation filtration has
`E₁^{p,q} = Ext⁽2p+q⁾(M, H^{-p}(K))`. -/
@[stacks 0G1Y "truncation filtration"] #check
  fun (M K : DerivedCategory A) ↦
    (DerivedCategory.Ext.Target.Truncation.existsSpectralSequence M K :
      ∃ (F : FilteredComplex AddCommGrpCat.{t})
        (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0),
        DerivedCategory.Ext.Target.Truncation.IsSpectralSequence M K F E)

/- Remark 19.13.9 (2): after renumbering,
`E'_r^{i,j} = E_{r-1}^{-j,i+2j}` for `r ≥ 2`, and
`E'_2^{i,j} = Ext⁽i⁾(M, H^j(K))`, independently of a representative for `K`. -/
@[stacks 0G1Y "renumbered cohomology spectral sequence"] #check
  fun (M K : DerivedCategory A) ↦
    (DerivedCategory.Ext.Target.Cohomology.existsSpectralSequence M K :
      ∃ (F : FilteredComplex AddCommGrpCat.{t})
        (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0)
        (E' : E₂CohomologicalSpectralSequence AddCommGrpCat.{t}),
        DerivedCategory.Ext.Target.Cohomology.IsSpectralSequence M K F E E')

/- Remark 19.13.9 (3): the stupid filtration has `E₁^{p,q} = Ext⁽q⁾(M, K^p)`. -/
@[stacks 0G1Y "stupid filtration"] #check
  fun (M : DerivedCategory A) (K : CochainComplex A ℤ) ↦
    (DerivedCategory.Ext.Target.Stupid.existsSpectralSequence M K :
      ∃ (F : FilteredComplex AddCommGrpCat.{t})
        (E : CohomologicalSpectralSequence AddCommGrpCat.{t} 0),
        DerivedCategory.Ext.Target.Stupid.IsSpectralSequence M K F E)
