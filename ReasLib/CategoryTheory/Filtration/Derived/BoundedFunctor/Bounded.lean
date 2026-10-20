/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization.Lift
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded functors on finite filtered derived categories

This module is the two-sided bounded counterpart of the `Plus` and `Minus` APIs.  Concrete
homotopy functors, inversion conditions, and localization lifts are separate, and every descended
functor receives its inversion certificate explicitly.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory C] [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

namespace Bounded.GradedPiece

/-- The bounded homotopy-to-derived functor given by the `p`-th associated-graded piece. -/
@[stacks 05S6 "bounded finite filtered graded-piece functor"]
noncomputable def homotopy (p : ℤ) :
    HomotopyCategory.Bounded (FilteredObject.Finite.category C) ⥤ DerivedCategory.Bounded C :=
  (FilteredObject.Finite.AssociatedGraded.functor C ⋙
      GradedObject.eval p).mapHomotopyCategoryBounded ⋙
    DerivedCategory.Bounded.Qh C

/-- The inversion condition needed to descend the bounded `p`-th graded-piece functor. -/
@[stacks 05S6 "bounded finite filtered graded-piece functor"]
abbrev Inverts (p : ℤ) : Prop := (Bounded.QuasiIso C).IsInvertedBy (homotopy C p)

/-- The bounded `p`-th graded-piece source inverts filtered quasi-isomorphisms. -/
@[stacks 05S6 "bounded finite filtered graded-piece functor"]
theorem inverts (p : ℤ) : Inverts C p := sorry

/-- The `p`-th graded-piece functor on the bounded finite filtered derived category. -/
@[stacks 05S6 "bounded finite filtered graded-piece functor"]
noncomputable def lift (p : ℤ) (h_piece : Inverts C p) :
    Bounded.Category C h_inverts ⥤ DerivedCategory.Bounded C :=
  Bounded.Quotient.lift C h_inverts (homotopy C p) h_piece

/-- The factorization of `lift` through the bounded quotient functor. -/
@[stacks 05S6 "bounded finite filtered graded-piece functor"]
noncomputable def facIso (p : ℤ) (h_piece : Inverts C p) :
    Bounded.Quotient.functor C h_inverts ⋙ lift C h_inverts p h_piece ≅ homotopy C p :=
  Bounded.Quotient.facIso C h_inverts (homotopy C p) h_piece

/-- The canonical bounded graded-piece lift, using the library inversion certificates. -/
@[stacks 05S6 "canonical finite filtered graded-piece functor"]
noncomputable abbrev canonicalLift (p : ℤ) :
    Bounded.canonicalCategory C ⥤ DerivedCategory.Bounded C :=
  lift C (AssociatedGraded.inverts C) p (inverts C p)

/-- The factorization isomorphism for the canonical bounded graded-piece lift. -/
@[stacks 05S6 "canonical finite filtered graded-piece functor"]
noncomputable abbrev canonicalFacIso (p : ℤ) :
    Bounded.Quotient.canonicalFunctor C ⋙ canonicalLift C p ≅ homotopy C p :=
  facIso C (AssociatedGraded.inverts C) p (inverts C p)

end Bounded.GradedPiece

namespace Bounded.Forget

/-- The bounded homotopy-to-derived functor obtained by forgetting the filtration. -/
@[stacks 05S6 "bounded finite filtered forgetful functor"]
noncomputable def homotopy :
    HomotopyCategory.Bounded (FilteredObject.Finite.category C) ⥤ DerivedCategory.Bounded C :=
  (FilteredObject.Finite.Forget.functor C).mapHomotopyCategoryBounded ⋙
    DerivedCategory.Bounded.Qh C

/-- The inversion condition needed to descend the bounded forgetful functor. -/
@[stacks 05S6 "bounded finite filtered forgetful functor"]
abbrev Inverts : Prop := (Bounded.QuasiIso C).IsInvertedBy (homotopy C)

/-- Forgetting a finite filtration inverts bounded filtered quasi-isomorphisms. -/
@[stacks 05S6 "bounded finite filtered forgetful functor"]
theorem inverts : Inverts C := sorry

/-- The forgetful functor from the bounded finite filtered derived category. -/
@[stacks 05S6 "bounded finite filtered forgetful functor"]
noncomputable def lift (h_forget : Inverts C) :
    Bounded.Category C h_inverts ⥤ DerivedCategory.Bounded C :=
  Bounded.Quotient.lift C h_inverts (homotopy C) h_forget

/-- The factorization of `lift` through the bounded quotient functor. -/
@[stacks 05S6 "bounded finite filtered forgetful functor"]
noncomputable def facIso (h_forget : Inverts C) :
    Bounded.Quotient.functor C h_inverts ⋙ lift C h_inverts h_forget ≅ homotopy C :=
  Bounded.Quotient.facIso C h_inverts (homotopy C) h_forget

/-- The canonical bounded forgetful lift, using the library inversion certificates. -/
@[stacks 05S6 "canonical finite filtered forgetful functor"]
noncomputable abbrev canonicalLift :
    Bounded.canonicalCategory C ⥤ DerivedCategory.Bounded C :=
  lift C (AssociatedGraded.inverts C) (inverts C)

/-- The factorization isomorphism for the canonical bounded forgetful lift. -/
@[stacks 05S6 "canonical finite filtered forgetful functor"]
noncomputable abbrev canonicalFacIso :
    Bounded.Quotient.canonicalFunctor C ⋙ canonicalLift C ≅ homotopy C :=
  facIso C (AssociatedGraded.inverts C) (inverts C)

end Bounded.Forget

end CategoryTheory.FilteredObject.FiniteDerived
