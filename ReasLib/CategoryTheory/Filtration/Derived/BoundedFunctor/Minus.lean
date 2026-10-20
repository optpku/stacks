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
# Bounded-above functors on finite filtered derived categories

The homotopy-level graded-piece and forgetful functors are separated from their inversion
conditions and localization lifts.  Each descended functor takes its inversion certificate
explicitly, matching the data/Prop boundary used by the bounded-below API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory C] [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

namespace Minus.GradedPiece

/-- The bounded-above homotopy-to-derived functor given by the `p`-th associated-graded piece. -/
@[stacks 05S6 "bounded-above finite filtered graded-piece functor"]
noncomputable def homotopy (p : ℤ) :
    HomotopyCategory.Minus (FilteredObject.Finite.category C) ⥤ DerivedCategory.Minus C :=
  (FilteredObject.Finite.AssociatedGraded.functor C ⋙
      GradedObject.eval p).mapHomotopyCategoryMinus ⋙
    DerivedCategory.Minus.Qh C

/-- The inversion condition needed to descend the bounded-above `p`-th graded-piece functor. -/
@[stacks 05S6 "bounded-above finite filtered graded-piece functor"]
abbrev Inverts (p : ℤ) : Prop := (Minus.QuasiIso C).IsInvertedBy (homotopy C p)

/-- The bounded-above `p`-th graded-piece source inverts filtered quasi-isomorphisms. -/
@[stacks 05S6 "bounded-above finite filtered graded-piece functor"]
theorem inverts (p : ℤ) : Inverts C p := sorry

/-- The `p`-th graded-piece functor on the bounded-above finite filtered derived category. -/
@[stacks 05S6 "bounded-above finite filtered graded-piece functor"]
noncomputable def lift (p : ℤ) (h_piece : Inverts C p) :
    Minus.Category C h_inverts ⥤ DerivedCategory.Minus C :=
  Minus.Quotient.lift C h_inverts (homotopy C p) h_piece

/-- The factorization of `lift` through the bounded-above quotient functor. -/
@[stacks 05S6 "bounded-above finite filtered graded-piece functor"]
noncomputable def facIso (p : ℤ) (h_piece : Inverts C p) :
    Minus.Quotient.functor C h_inverts ⋙ lift C h_inverts p h_piece ≅ homotopy C p :=
  Minus.Quotient.facIso C h_inverts (homotopy C p) h_piece

/-- The canonical bounded-above graded-piece lift, using the library inversion certificates. -/
@[stacks 05S6 "canonical bounded-above finite filtered graded-piece functor"]
noncomputable abbrev canonicalLift (p : ℤ) :
    Minus.canonicalCategory C ⥤ DerivedCategory.Minus C :=
  lift C (AssociatedGraded.inverts C) p (inverts C p)

/-- The factorization isomorphism for the canonical bounded-above graded-piece lift. -/
@[stacks 05S6 "canonical bounded-above finite filtered graded-piece functor"]
noncomputable abbrev canonicalFacIso (p : ℤ) :
    Minus.Quotient.canonicalFunctor C ⋙ canonicalLift C p ≅ homotopy C p :=
  facIso C (AssociatedGraded.inverts C) p (inverts C p)

end Minus.GradedPiece

namespace Minus.Forget

/-- The bounded-above homotopy-to-derived functor obtained by forgetting the filtration. -/
@[stacks 05S6 "bounded-above finite filtered forgetful functor"]
noncomputable def homotopy :
    HomotopyCategory.Minus (FilteredObject.Finite.category C) ⥤ DerivedCategory.Minus C :=
  (FilteredObject.Finite.Forget.functor C).mapHomotopyCategoryMinus ⋙
    DerivedCategory.Minus.Qh C

/-- The inversion condition needed to descend the bounded-above forgetful functor. -/
@[stacks 05S6 "bounded-above finite filtered forgetful functor"]
abbrev Inverts : Prop := (Minus.QuasiIso C).IsInvertedBy (homotopy C)

/-- Forgetting a finite filtration inverts bounded-above filtered quasi-isomorphisms. -/
@[stacks 05S6 "bounded-above finite filtered forgetful functor"]
theorem inverts : Inverts C := sorry

/-- The forgetful functor from the bounded-above finite filtered derived category. -/
@[stacks 05S6 "bounded-above finite filtered forgetful functor"]
noncomputable def lift (h_forget : Inverts C) :
    Minus.Category C h_inverts ⥤ DerivedCategory.Minus C :=
  Minus.Quotient.lift C h_inverts (homotopy C) h_forget

/-- The factorization of `lift` through the bounded-above quotient functor. -/
@[stacks 05S6 "bounded-above finite filtered forgetful functor"]
noncomputable def facIso (h_forget : Inverts C) :
    Minus.Quotient.functor C h_inverts ⋙ lift C h_inverts h_forget ≅ homotopy C :=
  Minus.Quotient.facIso C h_inverts (homotopy C) h_forget

/-- The canonical bounded-above forgetful lift, using the library inversion certificates. -/
@[stacks 05S6 "canonical bounded-above finite filtered forgetful functor"]
noncomputable abbrev canonicalLift :
    Minus.canonicalCategory C ⥤ DerivedCategory.Minus C :=
  lift C (AssociatedGraded.inverts C) (inverts C)

/-- The factorization isomorphism for the canonical bounded-above forgetful lift. -/
@[stacks 05S6 "canonical bounded-above finite filtered forgetful functor"]
noncomputable abbrev canonicalFacIso :
    Minus.Quotient.canonicalFunctor C ⋙ canonicalLift C ≅ homotopy C :=
  facIso C (AssociatedGraded.inverts C) (inverts C)

end Minus.Forget

end CategoryTheory.FilteredObject.FiniteDerived
