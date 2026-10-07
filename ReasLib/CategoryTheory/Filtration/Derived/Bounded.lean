module

public import ReasLib.CategoryTheory.Filtration.Derived.AssociatedGraded
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded Finite Filtered Derived Categories

These are the full subcategories of the finite filtered derived category detected by the standard
t-structure after applying derived associated graded.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe v u

namespace CategoryTheory

namespace FilteredObject

namespace FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]

namespace Plus

/-- The bounded-below property on the finite filtered derived category, detected after derived
associated graded. -/
@[stacks 05S4 "bounded below finite filtered derived category"]
abbrev property (h_inverts : AssociatedGraded.Inverts C) :
    ObjectProperty (Quotient.Category C) :=
  (t.plus : ObjectProperty (DerivedCategory (GradedObject ℤ C))).inverseImage
    (AssociatedGraded.lift C h_inverts)

/-- The bounded-below finite filtered derived category. -/
@[stacks 05S4 "bounded below finite filtered derived category"]
abbrev Category (h_inverts : AssociatedGraded.Inverts C) : Type (max u v) :=
  (property C h_inverts).FullSubcategory

/-- The canonical bounded-below property, using the library's associated-graded inversion proof.

This alias is the proof-stable entry point for downstream constructions.  APIs that need an
alternative certificate continue to use `property C h_inverts`. -/
@[stacks 05S4 "canonical bounded below finite filtered derived category"]
abbrev canonicalProperty : ObjectProperty (Quotient.Category C) :=
  property C (AssociatedGraded.inverts C)

/-- The canonical bounded-below finite filtered derived category. -/
@[stacks 05S4 "canonical bounded below finite filtered derived category"]
abbrev canonicalCategory : Type (max u v) :=
  Category C (AssociatedGraded.inverts C)

end Plus

namespace Minus

/-- The bounded-above property on the finite filtered derived category, detected after derived
associated graded. -/
@[stacks 05S4 "bounded above finite filtered derived category"]
abbrev property (h_inverts : AssociatedGraded.Inverts C) :
    ObjectProperty (Quotient.Category C) :=
  (t.minus : ObjectProperty (DerivedCategory (GradedObject ℤ C))).inverseImage
    (AssociatedGraded.lift C h_inverts)

/-- The bounded-above finite filtered derived category. -/
@[stacks 05S4 "bounded above finite filtered derived category"]
abbrev Category (h_inverts : AssociatedGraded.Inverts C) : Type (max u v) :=
  (property C h_inverts).FullSubcategory

/-- The canonical bounded-above property, using the library's associated-graded inversion proof. -/
@[stacks 05S4 "canonical bounded above finite filtered derived category"]
abbrev canonicalProperty : ObjectProperty (Quotient.Category C) :=
  property C (AssociatedGraded.inverts C)

/-- The canonical bounded-above finite filtered derived category. -/
@[stacks 05S4 "canonical bounded above finite filtered derived category"]
abbrev canonicalCategory : Type (max u v) :=
  Category C (AssociatedGraded.inverts C)

end Minus

namespace Bounded

/-- The bounded property on the finite filtered derived category, detected after derived
associated graded. -/
@[stacks 05S4 "bounded finite filtered derived category"]
abbrev property (h_inverts : AssociatedGraded.Inverts C) :
    ObjectProperty (Quotient.Category C) :=
  (t.bounded : ObjectProperty (DerivedCategory (GradedObject ℤ C))).inverseImage
    (AssociatedGraded.lift C h_inverts)

/-- The bounded finite filtered derived category. -/
@[stacks 05S4 "bounded finite filtered derived category"]
abbrev Category (h_inverts : AssociatedGraded.Inverts C) : Type (max u v) :=
  (property C h_inverts).FullSubcategory

/-- The canonical bounded property, using the library's associated-graded inversion proof. -/
@[stacks 05S4 "canonical finite filtered derived category"]
abbrev canonicalProperty : ObjectProperty (Quotient.Category C) :=
  property C (AssociatedGraded.inverts C)

/-- The canonical bounded finite filtered derived category. -/
@[stacks 05S4 "canonical finite filtered derived category"]
abbrev canonicalCategory : Type (max u v) :=
  Category C (AssociatedGraded.inverts C)

end Bounded

end FiniteDerived

end FilteredObject

end CategoryTheory
