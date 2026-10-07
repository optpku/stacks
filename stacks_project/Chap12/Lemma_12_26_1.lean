module

public import Mathlib.Algebra.Category.Grp.AB
public import ReasLib.CategoryTheory.Homology.DoubleComplex.CoaugmentedResolution
import StacksCheckRecall

/-!
# Lemma 12.26.1

Source-facing checks for a coaugmented cochain complex of cochain complexes and its coproduct
total. The reindexed bicomplex and comparison map are owned by
`HomologicalComplex₂.CoaugmentedResolution` in `ReasLib`.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex

noncomputable section

universe u

variable {M : CochainComplex AddCommGrpCat.{u} ℤ}
variable (A : CochainComplex (CochainComplex AddCommGrpCat.{u} ℤ) ℕ)
variable (ι : M ⟶ A.X 0) (hι : ι ≫ A.d 0 1 = 0)

/- The source row is reindexed by the canonical embedding `ℕ ↪ ℤ`; its zeroth column is
canonically the original complex `A.X 0`. -/
#check (HomologicalComplex₂.CoaugmentedResolution.bicomplex A :
  HomologicalComplex₂ AddCommGrpCat (up ℤ) (up ℤ))
#check (HomologicalComplex₂.CoaugmentedResolution.zeroColumnIso A :
  (HomologicalComplex₂.CoaugmentedResolution.bicomplex A).X 0 ≅ A.X 0)

/- The source coaugmentation is transported to the zeroth column of the reindexed bicomplex. -/
#check (HomologicalComplex₂.CoaugmentedResolution.zeroColumnMap A ι :
  M ⟶ (HomologicalComplex₂.CoaugmentedResolution.bicomplex A).X 0)

/- The coaugmentation relation is exposed as a morphism equality.  The neutral zero-column API
converts it to the componentwise cycle condition required by totalization. -/
#check (HomologicalComplex₂.CoaugmentedResolution.zeroColumnMap_comp_d A ι hι :
  HomologicalComplex₂.CoaugmentedResolution.zeroColumnMap A ι ≫
    (HomologicalComplex₂.CoaugmentedResolution.bicomplex A).d 0 1 = 0)
#check ((HomologicalComplex₂.ZeroColumn.comp_d_eq_zero_iff
  (A := HomologicalComplex₂.CoaugmentedResolution.bicomplex A)
  (HomologicalComplex₂.CoaugmentedResolution.zeroColumnMap A ι)).mp
  (HomologicalComplex₂.CoaugmentedResolution.zeroColumnMap_comp_d A ι hι) :
  ∀ q : ℤ,
    (HomologicalComplex₂.CoaugmentedResolution.zeroColumnMap A ι).f q ≫
      ((HomologicalComplex₂.CoaugmentedResolution.bicomplex A).d 0 1).f q = 0)

/- The comparison map is concrete data obtained from the generic zeroth-column-to-total map. -/
#check (HomologicalComplex₂.CoaugmentedResolution.ToTotal.map A ι hι :
  M ⟶ HomologicalComplex₂.total
    (HomologicalComplex₂.CoaugmentedResolution.bicomplex A) (up ℤ))

section

variable [Mono ι]
variable
  (hExact₀ : (HomologicalComplex₂.CoaugmentedResolution.shortComplex A ι hι).Exact)
  (hExact : ∀ n : ℕ, A.ExactAt (n + 1))

/- Lemma 12.26.1 [0E1Q]: an exact coaugmented cochain complex of cochain complexes of abelian
groups computes its source by the coproduct total of the associated double complex. -/
@[stacks 0E1Q]
#check (HomologicalComplex₂.CoaugmentedResolution.ToTotal.quasiIso_of_exact
  A ι hι hExact₀ hExact :
    QuasiIso (HomologicalComplex₂.CoaugmentedResolution.ToTotal.map A ι hι))

end
