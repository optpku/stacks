module

public import ReasLib.CategoryTheory.Homology.DegreewiseSplit.Chain
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopies Between Degreewise-Split Chain Connecting Maps

Changing a degreewise splitting changes the associated chain connecting morphism by a homotopy
whose components are the section corrections.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

universe v u

namespace ChainComplex

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace DegreewiseSplit.Homotopy

/-- The component family underlying the homotopy between chain connecting morphisms after a
section correction. -/
def component (S : ShortComplex (ChainComplex C ℤ))
    (h : ∀ n : ℤ, (S.degreewise n).X₃ ⟶ (S.degreewise n).X₁)
    (i j : ℤ) : S.X₃.X i ⟶ (S.X₁⟦(-1 : ℤ)⟧).X j :=
  if e : j = i + 1 then
    h i ≫ (Shift.MinusOne.succXIso S.X₁ i).inv ≫
      ((S.X₁⟦(-1 : ℤ)⟧).XIsoOfEq e.symm).hom
  else 0

/-- The correction component vanishes away from adjacent chain degrees. -/
theorem component_zero (S : ShortComplex (ChainComplex C ℤ))
    (h : ∀ n : ℤ, (S.degreewise n).X₃ ⟶ (S.degreewise n).X₁)
    (i j : ℤ) (hij : ¬(ComplexShape.down ℤ).Rel j i) :
    component S h i j = 0 := sorry

/-- The correction components satisfy the homotopy equation for the two chain connecting
morphisms. -/
theorem component_comm (S : ShortComplex (ChainComplex C ℤ))
    (σ σ' : ∀ n : ℤ, (S.degreewise n).Splitting)
    (h : ∀ n : ℤ, (S.degreewise n).X₃ ⟶ (S.degreewise n).X₁)
    (hs : ∀ n : ℤ, (σ n).IsSectionCorrection (σ' n) (h n)) (i : ℤ) :
    (homOfDegreewiseSplit S σ).f i =
      dNext i (component S h) + prevD i (component S h) +
        (homOfDegreewiseSplit S σ').f i := sorry

/-- Correcting a degreewise splitting yields a homotopy between the corresponding chain
connecting morphisms. -/
@[stacks 011F]
def ofCorrection (S : ShortComplex (ChainComplex C ℤ))
    (σ σ' : ∀ n : ℤ, (S.degreewise n).Splitting)
    (h : ∀ n : ℤ, (S.degreewise n).X₃ ⟶ (S.degreewise n).X₁)
    (hs : ∀ n : ℤ, (σ n).IsSectionCorrection (σ' n) (h n)) :
    Homotopy (homOfDegreewiseSplit S σ) (homOfDegreewiseSplit S σ') :=
  Homotopy.mk (component S h) (component_zero S h)
    (component_comm S σ σ' h hs)

/-- The degree-`n` component of `ofCorrection` is `h n` under the standard shift
identification. -/
theorem component_comp_shiftIso (S : ShortComplex (ChainComplex C ℤ))
    (σ σ' : ∀ n : ℤ, (S.degreewise n).Splitting)
    (h : ∀ n : ℤ, (S.degreewise n).X₃ ⟶ (S.degreewise n).X₁)
    (hs : ∀ n : ℤ, (σ n).IsSectionCorrection (σ' n) (h n)) (n : ℤ) :
    (ofCorrection S σ σ' h hs).hom n (n + 1) ≫
        (Shift.MinusOne.succXIso S.X₁ n).hom =
      h n := sorry

end DegreewiseSplit.Homotopy

end


end ChainComplex
