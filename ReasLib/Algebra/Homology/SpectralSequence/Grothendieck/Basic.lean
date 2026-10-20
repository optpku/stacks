/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Homology
public import ReasLib.CategoryTheory.Filtration.Complex.Realization.Abutment
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Grothendieck Spectral Sequences

This file owns the representation-independent target objects and the chosen realization of a
Grothendieck spectral sequence.  The realization is parameterized by the two derived functors
that occur in the page-two and abutment formulas; the construction from a composable pair of
left-exact functors is kept in a separate leaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA wB wC v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Grothendieck

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Abelian A] [Abelian B] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C] [HasInjectiveResolutions B]

/-- The `(p, q)` page-two target as a functor of the bounded-below derived object. -/
@[stacks 015N "Grothendieck spectral-sequence page-two functor"]
noncomputable def pageTwoFunctor
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (p : ℕ) (q : ℤ) : DerivedCategory.Plus A ⥤ C :=
  RF ⋙ DerivedCategory.Plus.homologyFunctor B q ⋙ G.rightDerived p

/-- The `(p, q)` object on the second page of the Grothendieck spectral sequence attached to
`G`, a derived functor `RF`, and `X`. -/
@[stacks 015N "Grothendieck spectral-sequence page two"]
noncomputable abbrev pageTwo
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (X : DerivedCategory.Plus A) (p : ℕ) (q : ℤ) : C :=
  (pageTwoFunctor G RF p q).obj X

/-- Evaluation of `pageTwoFunctor` recovers the page-two target. -/
@[simp, stacks 015N "Grothendieck spectral-sequence page-two functor"]
theorem pageTwoFunctor_obj
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (p : ℕ) (q : ℤ) (X : DerivedCategory.Plus A) :
    (pageTwoFunctor G RF p q).obj X = pageTwo G RF X p q := sorry

/-- The degreewise abutment as a functor of the bounded-below derived object. -/
@[stacks 015N "Grothendieck spectral-sequence abutment functor"]
noncomputable def abutmentFunctor
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (n : ℤ) :
    DerivedCategory.Plus A ⥤ C :=
  RGF ⋙ DerivedCategory.Plus.homologyFunctor C n

/-- The degree-`n` abutment object of a Grothendieck spectral sequence attached to a derived
functor for the composite. -/
@[stacks 015N "Grothendieck spectral-sequence abutment"]
noncomputable abbrev abutment
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C)
    (X : DerivedCategory.Plus A) (n : ℤ) : C :=
  (abutmentFunctor RGF n).obj X

/-- Evaluation of `abutmentFunctor` recovers the abutment target. -/
@[simp, stacks 015N "Grothendieck spectral-sequence abutment functor"]
theorem abutmentFunctor_obj
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C) (n : ℤ)
    (X : DerivedCategory.Plus A) :
    (abutmentFunctor RGF n).obj X = abutment RGF X n := sorry

/-- A chosen Grothendieck spectral-sequence realization with its page-two and abutment
comparisons. The associated filtered-complex, boundedness, finite-filtration, and convergence
data are inherited from the neutral filtered spectral-sequence realization. -/
@[stacks 015N "Grothendieck spectral-sequence realization"]
structure SpectralSequence
    (G : B ⥤ C) [G.Additive] (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (RGF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus C)
    (X : DerivedCategory.Plus A)
    extends toWithAbutment :
      FilteredComplex.SpectralSequence.Realization.WithAbutment
        (abutmentFunctor RGF) X where
  /-- The canonical identification of the second page. -/
  pageTwoIso : ∀ (p : ℕ) (q : ℤ),
    (sequence.page 2).X (Int.ofNat p, q) ≅ pageTwo G RF X p q
  /-- The actual second page has no terms in negative first degree. -/
  pageTwo_isZero_of_neg : ∀ (p q : ℤ), p < 0 →
    IsZero ((sequence.page 2).X (p, q))

end CategoryTheory.Functor.RightDerived.Grothendieck
