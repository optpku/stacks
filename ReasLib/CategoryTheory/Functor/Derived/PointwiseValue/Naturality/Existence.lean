module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of pointwise derived existence

Pointwise Kan-extension existence is invariant under natural isomorphism of the source
functor.  This leaf specializes the general Mathlib transport API to pointwise left- and
right-derived functors, both at one object and globally.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- Pointwise right-derived existence at `X` transports along a natural isomorphism of
source functors. -/
@[stacks 05SA "pointwise right-derived existence under natural isomorphism"]
theorem HasPointwiseRightDerivedFunctorAt.of_natIso
    (S : MorphismProperty C) {F G : C ⥤ D} (X : C)
    [F.HasPointwiseRightDerivedFunctorAt S X] (e : F ≅ G) :
    G.HasPointwiseRightDerivedFunctorAt S X := sorry

/-- Pointwise right-derived existence at `X` is invariant under a natural isomorphism of
source functors. -/
@[stacks 05SA "pointwise right-derived existence iff under natural isomorphism"]
theorem hasPointwiseRightDerivedFunctorAt_iff_of_natIso
    (S : MorphismProperty C) {F G : C ⥤ D} (X : C) (e : F ≅ G) :
    F.HasPointwiseRightDerivedFunctorAt S X ↔
      G.HasPointwiseRightDerivedFunctorAt S X := sorry

/-- Global pointwise right-derived existence transports along a natural isomorphism of source
functors. -/
@[stacks 05SA "global pointwise right-derived existence under natural isomorphism"]
theorem HasPointwiseRightDerivedFunctor.of_iso
    (S : MorphismProperty C) {F G : C ⥤ D}
    [F.HasPointwiseRightDerivedFunctor S] (e : F ≅ G) :
    G.HasPointwiseRightDerivedFunctor S := sorry

/-- Global pointwise right-derived existence is invariant under a natural isomorphism of
source functors. -/
@[stacks 05SA "global pointwise right-derived existence iff under natural isomorphism"]
theorem hasPointwiseRightDerivedFunctor_iff_of_iso
    (S : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G) :
    F.HasPointwiseRightDerivedFunctor S ↔
      G.HasPointwiseRightDerivedFunctor S := sorry

/-- Pointwise left-derived existence at `X` transports along a natural isomorphism of source
functors. -/
@[stacks 05SA "pointwise left-derived existence under natural isomorphism"]
theorem HasPointwiseLeftDerivedFunctorAt.of_natIso
    (S : MorphismProperty C) {F G : C ⥤ D} (X : C)
    [F.HasPointwiseLeftDerivedFunctorAt S X] (e : F ≅ G) :
    G.HasPointwiseLeftDerivedFunctorAt S X := sorry

/-- Pointwise left-derived existence at `X` is invariant under a natural isomorphism of source
functors. -/
@[stacks 05SA "pointwise left-derived existence iff under natural isomorphism"]
theorem hasPointwiseLeftDerivedFunctorAt_iff_of_natIso
    (S : MorphismProperty C) {F G : C ⥤ D} (X : C) (e : F ≅ G) :
    F.HasPointwiseLeftDerivedFunctorAt S X ↔
      G.HasPointwiseLeftDerivedFunctorAt S X := sorry

/-- Global pointwise left-derived existence transports along a natural isomorphism of source
functors. -/
@[stacks 05SA "global pointwise left-derived existence under natural isomorphism"]
theorem HasPointwiseLeftDerivedFunctor.of_iso
    (S : MorphismProperty C) {F G : C ⥤ D}
    [F.HasPointwiseLeftDerivedFunctor S] (e : F ≅ G) :
    G.HasPointwiseLeftDerivedFunctor S := sorry

/-- Global pointwise left-derived existence is invariant under a natural isomorphism of source
functors. -/
@[stacks 05SA "global pointwise left-derived existence iff under natural isomorphism"]
theorem hasPointwiseLeftDerivedFunctor_iff_of_iso
    (S : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G) :
    F.HasPointwiseLeftDerivedFunctor S ↔
      G.HasPointwiseLeftDerivedFunctor S := sorry


end CategoryTheory.Functor
