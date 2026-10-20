/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization.Lift
public import ReasLib.CategoryTheory.Filtration.Derived.AssociatedGraded
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded associated-graded functors

This leaf supplies the whole associated-graded counterparts of the bounded graded-piece
functors.  Each boundedness convention exposes the homotopy-level functor, its inversion
condition, the descended localization lift, and the factorization isomorphism under the same
namespace layout.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts :
  _root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.Inverts C)

namespace Plus.AssociatedGraded

/-- The bounded-below homotopy-to-derived associated-graded functor. -/
@[stacks 05S6 "bounded-below finite filtered associated-graded functor"]
noncomputable def homotopy :
    HomotopyCategory.Plus (FilteredObject.Finite.category C) ⥤
      DerivedCategory.Plus (GradedObject ℤ C) :=
  (FilteredObject.Finite.AssociatedGraded.functor C).mapHomotopyCategoryPlus ⋙
    DerivedCategory.Plus.Qh

/-- The inversion condition for the bounded-below associated-graded functor. -/
@[stacks 05S6 "bounded-below finite filtered associated-graded functor"]
abbrev Inverts : Prop := (Plus.QuasiIso C).IsInvertedBy (homotopy C)

/-- The bounded-below associated-graded functor inverts filtered quasi-isomorphisms. -/
@[stacks 05S6 "bounded-below finite filtered associated-graded functor"]
theorem inverts : Inverts C := sorry

/-- Associated graded on the bounded-below finite filtered derived category. -/
@[stacks 05S6 "bounded-below finite filtered associated-graded functor"]
noncomputable def lift (h : Inverts C) :
    Plus.Category C h_inverts ⥤ DerivedCategory.Plus (GradedObject ℤ C) :=
  Plus.Quotient.lift C h_inverts (homotopy C) h

/-- The bounded-below associated-graded lift factors the homotopy-level functor. -/
@[stacks 05S6 "bounded-below finite filtered associated-graded functor"]
noncomputable def facIso (h : Inverts C) :
    Plus.Quotient.functor C h_inverts ⋙ lift C h_inverts h ≅ homotopy C :=
  Plus.Quotient.facIso C h_inverts (homotopy C) h

/-- The canonical bounded-below associated-graded lift, using the library inversion certificates. -/
@[stacks 05S6 "canonical bounded-below finite filtered associated-graded functor"]
noncomputable abbrev canonicalLift :
    Plus.canonicalCategory C ⥤ DerivedCategory.Plus (GradedObject ℤ C) :=
  lift C (_root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.inverts C)
    (inverts C)

/-- The factorization isomorphism for the canonical bounded-below associated-graded lift. -/
@[stacks 05S6 "canonical bounded-below finite filtered associated-graded functor"]
noncomputable abbrev canonicalFacIso :
    Plus.Quotient.canonicalFunctor C ⋙ canonicalLift C ≅ homotopy C :=
  facIso C (_root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.inverts C)
    (inverts C)

end Plus.AssociatedGraded

namespace Minus.AssociatedGraded

/-- The bounded-above homotopy-to-derived associated-graded functor. -/
@[stacks 05S6 "bounded-above finite filtered associated-graded functor"]
noncomputable def homotopy :
    HomotopyCategory.Minus (FilteredObject.Finite.category C) ⥤
      DerivedCategory.Minus (GradedObject ℤ C) :=
  (FilteredObject.Finite.AssociatedGraded.functor C).mapHomotopyCategoryMinus ⋙
    DerivedCategory.Minus.Qh (GradedObject ℤ C)

/-- The inversion condition for the bounded-above associated-graded functor. -/
@[stacks 05S6 "bounded-above finite filtered associated-graded functor"]
abbrev Inverts : Prop := (Minus.QuasiIso C).IsInvertedBy (homotopy C)

/-- The bounded-above associated-graded functor inverts filtered quasi-isomorphisms. -/
@[stacks 05S6 "bounded-above finite filtered associated-graded functor"]
theorem inverts : Inverts C := sorry

/-- Associated graded on the bounded-above finite filtered derived category. -/
@[stacks 05S6 "bounded-above finite filtered associated-graded functor"]
noncomputable def lift (h : Inverts C) :
    Minus.Category C h_inverts ⥤ DerivedCategory.Minus (GradedObject ℤ C) :=
  Minus.Quotient.lift C h_inverts (homotopy C) h

/-- The bounded-above associated-graded lift factors the homotopy-level functor. -/
@[stacks 05S6 "bounded-above finite filtered associated-graded functor"]
noncomputable def facIso (h : Inverts C) :
    Minus.Quotient.functor C h_inverts ⋙ lift C h_inverts h ≅ homotopy C :=
  Minus.Quotient.facIso C h_inverts (homotopy C) h

/-- The canonical bounded-above associated-graded lift, using the library inversion certificates. -/
@[stacks 05S6 "canonical bounded-above finite filtered associated-graded functor"]
noncomputable abbrev canonicalLift :
    Minus.canonicalCategory C ⥤ DerivedCategory.Minus (GradedObject ℤ C) :=
  lift C (_root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.inverts C)
    (inverts C)

/-- The factorization isomorphism for the canonical bounded-above associated-graded lift. -/
@[stacks 05S6 "canonical bounded-above finite filtered associated-graded functor"]
noncomputable abbrev canonicalFacIso :
    Minus.Quotient.canonicalFunctor C ⋙ canonicalLift C ≅ homotopy C :=
  facIso C (_root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.inverts C)
    (inverts C)

end Minus.AssociatedGraded

namespace Bounded.AssociatedGraded

/-- The bounded homotopy-to-derived associated-graded functor. -/
@[stacks 05S6 "bounded finite filtered associated-graded functor"]
noncomputable def homotopy :
    HomotopyCategory.Bounded (FilteredObject.Finite.category C) ⥤
      DerivedCategory.Bounded (GradedObject ℤ C) :=
  (FilteredObject.Finite.AssociatedGraded.functor C).mapHomotopyCategoryBounded ⋙
    DerivedCategory.Bounded.Qh (GradedObject ℤ C)

/-- The inversion condition for the bounded associated-graded functor. -/
@[stacks 05S6 "bounded finite filtered associated-graded functor"]
abbrev Inverts : Prop := (Bounded.QuasiIso C).IsInvertedBy (homotopy C)

/-- The bounded associated-graded functor inverts filtered quasi-isomorphisms. -/
@[stacks 05S6 "bounded finite filtered associated-graded functor"]
theorem inverts : Inverts C := sorry

/-- Associated graded on the bounded finite filtered derived category. -/
@[stacks 05S6 "bounded finite filtered associated-graded functor"]
noncomputable def lift (h : Inverts C) :
    Bounded.Category C h_inverts ⥤ DerivedCategory.Bounded (GradedObject ℤ C) :=
  Bounded.Quotient.lift C h_inverts (homotopy C) h

/-- The bounded associated-graded lift factors the homotopy-level functor. -/
@[stacks 05S6 "bounded finite filtered associated-graded functor"]
noncomputable def facIso (h : Inverts C) :
    Bounded.Quotient.functor C h_inverts ⋙ lift C h_inverts h ≅ homotopy C :=
  Bounded.Quotient.facIso C h_inverts (homotopy C) h

/-- The canonical bounded associated-graded lift, using the library inversion certificates. -/
@[stacks 05S6 "canonical finite filtered associated-graded functor"]
noncomputable abbrev canonicalLift :
    Bounded.canonicalCategory C ⥤ DerivedCategory.Bounded (GradedObject ℤ C) :=
  lift C (_root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.inverts C)
    (inverts C)

/-- The factorization isomorphism for the canonical bounded associated-graded lift. -/
@[stacks 05S6 "canonical finite filtered associated-graded functor"]
noncomputable abbrev canonicalFacIso :
    Bounded.Quotient.canonicalFunctor C ⋙ canonicalLift C ≅ homotopy C :=
  facIso C (_root_.CategoryTheory.FilteredObject.FiniteDerived.AssociatedGraded.inverts C)
    (inverts C)

end Bounded.AssociatedGraded

end CategoryTheory.FilteredObject.FiniteDerived
