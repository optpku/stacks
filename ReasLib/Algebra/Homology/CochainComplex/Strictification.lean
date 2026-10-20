module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import ReasLib.Algebra.Homology.CochainComplex.Admissible

@[expose] public section

/-!
# Strictifying Homotopy-Commutative Squares of Cochain Complexes

The two strictification statements here are parameterized only by the
degreewise splitting hypothesis.  The admissibility variants then specialize
them to the canonical functor which forgets cochain differentials.
-/

open CategoryTheory ComplexShape HomologicalComplex HomotopyCategory

universe u v

namespace CochainComplex

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {A B D E : CochainComplex C ℤ}

/-- A homotopy-commutative square of cochain complexes with termwise split-monic top map can be
strictified by changing its right map within its homotopy class. -/
@[stacks 014H "right strictification by a termwise split monomorphism"]
theorem exists_homotopic_rightMap_of_termwiseSplitMono
    {f : A ⟶ B} {a : A ⟶ D} {b : B ⟶ E} {g : D ⟶ E}
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hf : ∀ n : ℤ, IsSplitMono (f.f n)) :
    ∃ (b' : B ⟶ E) (_ : Homotopy b b'), CommSq f a b' g := sorry

/-- A homotopy-commutative square of cochain complexes with termwise split-epic bottom map can be
strictified by changing its left map within its homotopy class. -/
@[stacks 014H "left strictification by a termwise split epimorphism"]
theorem exists_homotopic_leftMap_of_termwiseSplitEpi
    {f : A ⟶ B} {a : A ⟶ D} {b : B ⟶ E} {g : D ⟶ E}
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hg : ∀ n : ℤ, IsSplitEpi (g.f n)) :
    ∃ (a' : A ⟶ D) (_ : Homotopy a a'), CommSq f a' b g := sorry

/-- A homotopy-commutative square of cochain complexes whose top map is admissibly monic after
forgetting differentials can be strictified on the right. -/
@[stacks 014H "right admissible strictification",
  stacks 09JV "right strictification by an admissible monomorphism"]
theorem exists_homotopic_rightMap_of_admissibleMono
    {f : A ⟶ B} {a : A ⟶ D} {b : B ⟶ E} {g : D ⟶ E}
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hf : IsAdmissibleMono (forgetToGraded C) f) :
    ∃ (b' : B ⟶ E) (_ : Homotopy b b'), CommSq f a b' g := sorry

/-- A homotopy-commutative square of cochain complexes whose bottom map is admissibly epic after
forgetting differentials can be strictified on the left. -/
@[stacks 014H "left admissible strictification",
  stacks 09JV "left strictification by an admissible epimorphism"]
theorem exists_homotopic_leftMap_of_admissibleEpi
    {f : A ⟶ B} {a : A ⟶ D} {b : B ⟶ E} {g : D ⟶ E}
    (hcomm : Homotopy (f ≫ b) (a ≫ g))
    (hg : IsAdmissibleEpi (forgetToGraded C) g) :
    ∃ (a' : A ⟶ D) (_ : Homotopy a a'), CommSq f a' b g := sorry

section HomotopyCategoryView

/-- The homotopy-category square formulation of strictification on the right.  The replacement
can be chosen to represent the original right map after localization. -/
@[stacks 014H "right strictification in the homotopy category"]
theorem exists_rightMap_eq_in_homotopyCategory_of_termwiseSplitMono
    {f : A ⟶ B} {a : A ⟶ D} {b : B ⟶ E} {g : D ⟶ E}
    (sq : CommSq ((quotient C (up ℤ)).map f) ((quotient C (up ℤ)).map a)
      ((quotient C (up ℤ)).map b) ((quotient C (up ℤ)).map g))
    (hf : ∀ n : ℤ, IsSplitMono (f.f n)) :
    ∃ b' : B ⟶ E,
      (quotient C (up ℤ)).map b = (quotient C (up ℤ)).map b' ∧ CommSq f a b' g := sorry

/-- The homotopy-category square formulation of strictification on the left.  The replacement
can be chosen to represent the original left map after localization. -/
@[stacks 014H "left strictification in the homotopy category"]
theorem exists_leftMap_eq_in_homotopyCategory_of_termwiseSplitEpi
    {f : A ⟶ B} {a : A ⟶ D} {b : B ⟶ E} {g : D ⟶ E}
    (sq : CommSq ((quotient C (up ℤ)).map f) ((quotient C (up ℤ)).map a)
      ((quotient C (up ℤ)).map b) ((quotient C (up ℤ)).map g))
    (hg : ∀ n : ℤ, IsSplitEpi (g.f n)) :
    ∃ a' : A ⟶ D,
      (quotient C (up ℤ)).map a = (quotient C (up ℤ)).map a' ∧ CommSq f a' b g := sorry

end HomotopyCategoryView

end

end CochainComplex
