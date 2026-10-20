module

public import ReasLib.CategoryTheory.Homology.DegreewiseSplit.CochainHomotopy
import StacksCheckRecall

@[expose] public section

open CategoryTheory HomologicalComplex

universe v u

section Splitting

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {S : ShortComplex C}
variable (σ σ' : S.Splitting) (h k : S.X₃ ⟶ S.X₁)
variable (hs : σ.IsSectionCorrection σ' h)
variable (hk : σ'.r = σ.r + S.g ≫ k)

/- Lemma 12.14.12 (1): section and retraction corrections of two splittings are negatives of
one another.  The owner theorem is stated for an arbitrary short complex. -/
#check (CategoryTheory.ShortComplex.Splitting.retractionCorrection_eq_neg σ σ' h k hs hk :
  k = -h)

end Splitting

section Cochain

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (S : ShortComplex (CochainComplex C ℤ))
variable (σ σ' : ∀ n : ℤ, (S.degreewise n).Splitting)
variable (h : ∀ n : ℤ, (S.degreewise n).X₃ ⟶ (S.degreewise n).X₁)
variable (hs : ∀ n : ℤ, (σ n).IsSectionCorrection (σ' n) (h n))
variable (n : ℤ)

/- Lemma 12.14.12 (2): a degreewise section correction produces a homotopy from the corrected
cochain connecting morphism to the original one. -/
@[stacks 011L]
#check (CochainComplex.DegreewiseSplit.Homotopy.ofCorrection S σ σ' h hs :
  Homotopy (CochainComplex.homOfDegreewiseSplit S σ')
    (CochainComplex.homOfDegreewiseSplit S σ))

/- Its components are the negatives of the section corrections under the standard shift
identification. -/
#check (CochainComplex.DegreewiseSplit.Homotopy.component_comp_shiftIso S σ σ' h hs n :
  (CochainComplex.DegreewiseSplit.Homotopy.ofCorrection S σ σ' h hs).hom n (n - 1) ≫
      (S.X₁.shiftFunctorObjXIso 1 (n - 1) n (sub_add_cancel n 1).symm).hom = -h n)

end Cochain
