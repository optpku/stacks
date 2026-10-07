module

public import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization.Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-below functors on finite filtered derived categories

This module separates the concrete homotopy-level functors, their Prop-valued inversion
certificates, and the corresponding localization lifts.  In particular, descended functors take
their certificate explicitly, so their data does not silently depend on a provisional proof.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MorphismProperty

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory C] [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

namespace Plus.GradedPiece

/-- The bounded-below homotopy-to-derived functor given by the `p`-th associated-graded piece. -/
@[stacks 05S6 "bounded-below finite filtered graded-piece functor"]
noncomputable def homotopy (p : ℤ) :
    HomotopyCategory.Plus (FilteredObject.Finite.category C) ⥤ DerivedCategory.Plus C :=
  (FilteredObject.Finite.AssociatedGraded.functor C ⋙ GradedObject.eval p).mapHomotopyCategoryPlus ⋙
    DerivedCategory.Plus.Qh

/-- The inversion condition needed to descend the bounded-below `p`-th graded-piece functor. -/
@[stacks 05S6 "bounded-below finite filtered graded-piece functor"]
abbrev Inverts (p : ℤ) : Prop := (Plus.QuasiIso C).IsInvertedBy (homotopy C p)

/-- The bounded-below `p`-th graded-piece source inverts filtered quasi-isomorphisms. -/
@[stacks 05S6 "bounded-below finite filtered graded-piece functor"]
theorem inverts (p : ℤ) : Inverts C p := sorry

/-- The `p`-th graded-piece functor on the bounded-below finite filtered derived category. -/
@[stacks 05S6 "bounded-below finite filtered graded-piece functor"]
noncomputable def lift (p : ℤ) (h_piece : Inverts C p) :
    Plus.Category C h_inverts ⥤ DerivedCategory.Plus C :=
  Plus.Quotient.lift C h_inverts (homotopy C p) h_piece

/-- The factorization of `lift` through the bounded-below quotient functor. -/
@[stacks 05S6 "bounded-below finite filtered graded-piece functor"]
noncomputable def facIso (p : ℤ) (h_piece : Inverts C p) :
    Plus.Quotient.functor C h_inverts ⋙ lift C h_inverts p h_piece ≅ homotopy C p :=
  Plus.Quotient.facIso C h_inverts (homotopy C p) h_piece

/-- The canonical bounded-below graded-piece lift, using the library inversion certificates. -/
@[stacks 05S6 "canonical bounded-below finite filtered graded-piece functor"]
noncomputable abbrev canonicalLift (p : ℤ) :
    Plus.canonicalCategory C ⥤ DerivedCategory.Plus C :=
  lift C (AssociatedGraded.inverts C) p (inverts C p)

/-- The factorization isomorphism for the canonical bounded-below graded-piece lift. -/
@[stacks 05S6 "canonical bounded-below finite filtered graded-piece functor"]
noncomputable abbrev canonicalFacIso (p : ℤ) :
    Plus.Quotient.canonicalFunctor C ⋙ canonicalLift C p ≅ homotopy C p :=
  facIso C (AssociatedGraded.inverts C) p (inverts C p)

end Plus.GradedPiece

namespace Plus.Forget

/-- The bounded-below homotopy-to-derived functor obtained by forgetting the filtration. -/
@[stacks 05S6 "bounded-below finite filtered forgetful functor"]
noncomputable def homotopy :
    HomotopyCategory.Plus (FilteredObject.Finite.category C) ⥤ DerivedCategory.Plus C :=
  (FilteredObject.Finite.Forget.functor C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh

/-- The inversion condition needed to descend the bounded-below forgetful functor. -/
@[stacks 05S6 "bounded-below finite filtered forgetful functor"]
abbrev Inverts : Prop := (Plus.QuasiIso C).IsInvertedBy (homotopy C)

/-- Forgetting a finite filtration inverts bounded-below filtered quasi-isomorphisms. -/
@[stacks 05S6 "bounded-below finite filtered forgetful functor"]
theorem inverts : Inverts C := sorry

/-- The forgetful functor from the bounded-below finite filtered derived category. -/
@[stacks 05S6 "bounded-below finite filtered forgetful functor"]
noncomputable def lift (h_forget : Inverts C) :
    Plus.Category C h_inverts ⥤ DerivedCategory.Plus C :=
  Plus.Quotient.lift C h_inverts (homotopy C) h_forget

/-- The factorization of `lift` through the bounded-below quotient functor. -/
@[stacks 05S6 "bounded-below finite filtered forgetful functor"]
noncomputable def facIso (h_forget : Inverts C) :
    Plus.Quotient.functor C h_inverts ⋙ lift C h_inverts h_forget ≅ homotopy C :=
  Plus.Quotient.facIso C h_inverts (homotopy C) h_forget

/-- The canonical bounded-below forgetful lift, using the library inversion certificates. -/
@[stacks 05S6 "canonical bounded-below finite filtered forgetful functor"]
noncomputable abbrev canonicalLift :
    Plus.canonicalCategory C ⥤ DerivedCategory.Plus C :=
  lift C (AssociatedGraded.inverts C) (inverts C)

/-- The factorization isomorphism for the canonical bounded-below forgetful lift. -/
@[stacks 05S6 "canonical bounded-below finite filtered forgetful functor"]
noncomputable abbrev canonicalFacIso :
    Plus.Quotient.canonicalFunctor C ⋙ canonicalLift C ≅ homotopy C :=
  facIso C (AssociatedGraded.inverts C) (inverts C)

end Plus.Forget

end CategoryTheory.FilteredObject.FiniteDerived
