/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.DegreewiseSplit.Chain
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (S : ShortComplex (ChainComplex C ℤ))
variable (σ : ∀ n : ℤ, (S.degreewise n).Splitting) (n : ℤ)

/- Lemma 12.14.4: a degreewise splitting of a short complex of chain complexes determines the
canonical connecting map `S.X₃ ⟶ S.X₁⟦-1⟧`. -/
@[stacks 011D]
#check (ChainComplex.homOfDegreewiseSplit S σ :
  S.X₃ ⟶ S.X₁⟦(-1 : ℤ)⟧)

/- The raw component is available independently of the chain-map compatibility proof. -/
#check (ChainComplex.homOfDegreewiseSplit.coordinate S σ n :
  S.X₃.X n ⟶ S.X₁.X (n - 1))
#check (ChainComplex.homOfDegreewiseSplit.component S σ n :
  S.X₃.X n ⟶ (S.X₁⟦(-1 : ℤ)⟧).X n)
#check (ChainComplex.homOfDegreewiseSplit.component_comp_xIso S σ n :
  ChainComplex.homOfDegreewiseSplit.component S σ n ≫
      (ChainComplex.Shift.MinusOne.xIso S.X₁ n).hom =
    ChainComplex.homOfDegreewiseSplit.coordinate S σ n)
#check (ChainComplex.homOfDegreewiseSplit.component_eq S σ n :
  (ChainComplex.homOfDegreewiseSplit S σ).f n =
    ChainComplex.homOfDegreewiseSplit.component S σ n)

/- Its component is the textbook composite of the section, differential, and retraction. -/
#check (ChainComplex.homOfDegreewiseSplit_f S σ n :
  (ChainComplex.homOfDegreewiseSplit S σ).f n ≫
      (ChainComplex.Shift.MinusOne.xIso S.X₁ n).hom =
    (σ n).s ≫ S.X₂.d n (n - 1) ≫ (σ (n - 1)).r)
