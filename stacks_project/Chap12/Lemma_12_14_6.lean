/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.DegreewiseSplit.ChainHomotopy
import StacksCheckRecall

@[expose] public section

open CategoryTheory HomologicalComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (S : ShortComplex (ChainComplex C ℤ))
variable (σ σ' : ∀ n : ℤ, (S.degreewise n).Splitting)
variable (h : ∀ n : ℤ, (S.degreewise n).X₃ ⟶ (S.degreewise n).X₁)
variable (hs : ∀ n : ℤ, (σ n).IsSectionCorrection (σ' n) (h n))
variable (n : ℤ)

/- Lemma 12.14.6: a degreewise correction of the sections produces a homotopy between the
associated chain connecting morphisms. -/
@[stacks 011F]
#check (ChainComplex.DegreewiseSplit.Homotopy.ofCorrection S σ σ' h hs :
  Homotopy (ChainComplex.homOfDegreewiseSplit S σ)
    (ChainComplex.homOfDegreewiseSplit S σ'))

/- The homotopy components recover the given correction maps under the canonical shift
identification. -/
#check (ChainComplex.DegreewiseSplit.Homotopy.component_comp_shiftIso S σ σ' h hs n :
  (ChainComplex.DegreewiseSplit.Homotopy.ofCorrection S σ σ' h hs).hom n (n + 1) ≫
      (ChainComplex.Shift.MinusOne.succXIso S.X₁ n).hom = h n)
