/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed

/-!
# Representable universally closed morphisms of algebraic spaces

For a representable morphism of algebraic spaces, universal closedness of all
scheme base changes is equivalent to closedness on underlying point spaces
after every algebraic-space base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A representable morphism of algebraic spaces has universally closed scheme
base changes if and only if every algebraic-space base change induces a closed
map on underlying point spaces. -/
theorem universallyClosed_presheaf_iff_universallyClosed
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.UniversallyClosed : MorphismProperty Scheme.{u})).presheaf f ↔
      UniversallyClosed f :=
  sorry

/-- A representable morphism with universally closed scheme base changes is
universally closed as a morphism of algebraic spaces. -/
theorem universallyClosed_of_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.UniversallyClosed :
      MorphismProperty Scheme.{u})).presheaf f) :
    UniversallyClosed f :=
  sorry

/-- A representable universally closed morphism of algebraic spaces has
universally closed scheme base changes. -/
theorem universallyClosed_presheaf_of_universallyClosed
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : UniversallyClosed f) :
    (over (@AlgebraicGeometry.UniversallyClosed : MorphismProperty Scheme.{u})).presheaf f :=
  sorry

/-- A representable morphism has universally closed scheme base changes if and
only if every algebraic-space base change, expressed by an `IsPullback` square,
is a closed morphism. -/
theorem universallyClosed_presheaf_iff_isClosed_of_isPullback
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.UniversallyClosed : MorphismProperty Scheme.{u})).presheaf f ↔
      ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX g f → Closed pZ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
