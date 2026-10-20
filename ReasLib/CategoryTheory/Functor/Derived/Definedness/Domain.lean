module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Calculus
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Domains of Definition for Pointwise Derived Functors

For an arbitrary morphism property, pointwise left and right derived functors need only be
defined on an object property of the source category.  This leaf owns those object properties,
their full subcategories, and the restriction of the localization class.  It deliberately has no
triangulated-category hypotheses.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open MorphismProperty ObjectProperty

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

namespace Functor.RightDerived.Definedness

/-- the object property of points at which the pointwise right-derived value of
`F` with respect to `S` is defined. -/
@[stacks 05SU]
abbrev property : ObjectProperty D :=
  fun X ↦ F.HasPointwiseRightDerivedFunctorAt S X

/-- pointwise right-derived definedness is invariant under isomorphisms of source
objects. -/
@[stacks 05SU]
instance property.isClosedUnderIsomorphisms : IsClosedUnderIsomorphisms (property F S) := sorry

/-- the full subcategory on which the pointwise right-derived value of `F` is
defined. -/
@[stacks 05SE]
abbrev Domain := (property F S).FullSubcategory

/-- the localization class obtained by restricting `S` to the right-derived
defined full subcategory. -/
@[stacks 05SE]
abbrev system : MorphismProperty (Domain F S) :=
  fullSubcategoryLocalizationSystem (property F S) S

/-- an object in the right-derived-defined full subcategory supplies the corresponding
pointwise definedness fact to ambient typeclass search. -/
@[stacks 05SE]
instance Domain.hasPointwise (X : Domain F S) :
    F.HasPointwiseRightDerivedFunctorAt S X.obj :=
  X.property

/-- Right-derived definedness is inherited from the source of every denominator. -/
@[stacks 05SE]
instance property.inheritedFromSource : (property F S).InheritedFromSource S := sorry

/-- Right-derived definedness is inherited from the target of every denominator. -/
@[stacks 05SE]
instance property.inheritedFromTarget : (property F S).InheritedFromTarget S := sorry

end Functor.RightDerived.Definedness

namespace Functor.LeftDerived.Definedness

/-- the object property of points at which the pointwise left-derived value of
`F` with respect to `S` is defined. -/
@[stacks 05SU]
abbrev property : ObjectProperty D :=
  fun X ↦ F.HasPointwiseLeftDerivedFunctorAt S X

/-- pointwise left-derived definedness is invariant under isomorphisms of source
objects. -/
@[stacks 05SU]
instance property.isClosedUnderIsomorphisms : IsClosedUnderIsomorphisms (property F S) := sorry

/-- the full subcategory on which the pointwise left-derived value of `F` is
defined. -/
@[stacks 05SE]
abbrev Domain := (property F S).FullSubcategory

/-- the localization class obtained by restricting `S` to the left-derived
defined full subcategory. -/
@[stacks 05SE]
abbrev system : MorphismProperty (Domain F S) :=
  fullSubcategoryLocalizationSystem (property F S) S

/-- an object in the left-derived-defined full subcategory supplies the corresponding
pointwise definedness fact to ambient typeclass search. -/
@[stacks 05SE]
instance Domain.hasPointwise (X : Domain F S) :
    F.HasPointwiseLeftDerivedFunctorAt S X.obj :=
  X.property

/-- Left-derived definedness is inherited from the source of every denominator. -/
@[stacks 05SE]
instance property.inheritedFromSource : (property F S).InheritedFromSource S := sorry

/-- Left-derived definedness is inherited from the target of every denominator. -/
@[stacks 05SE]
instance property.inheritedFromTarget : (property F S).InheritedFromTarget S := sorry

end Functor.LeftDerived.Definedness


end CategoryTheory
