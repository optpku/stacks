/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap67.Lemma_67_6_3_UniversallyOpen

/-!
# Representable universally open morphisms of algebraic spaces

A representable morphism of algebraic spaces is universally open in the
sense of Section 67.3 if and only if every algebraic-space base change induces an
open map on underlying point spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.6.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is universally open in the
sense of Section 67.3 if and only if for every morphism of algebraic spaces
`Z ⟶ Y` the morphism of topological spaces `|Z ×_Y X| ⟶ |Z|` is open. -/
@[stacks 03Z1]
theorem universallyOpen_presheaf_iff_universallyOpen
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.UniversallyOpen : MorphismProperty Scheme.{u})).presheaf f ↔
      UniversallyOpen f :=
  sorry

/-- A representable morphism that is universally open in the sense of
Section 67.3 is universally open as a morphism of algebraic spaces. -/
theorem universallyOpen_of_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.UniversallyOpen :
      MorphismProperty Scheme.{u})).presheaf f) :
    UniversallyOpen f :=
  sorry

/-- A representable morphism that is universally open as a morphism of
algebraic spaces is universally open in the sense of Section 67.3. -/
theorem universallyOpen_presheaf_of_universallyOpen
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : UniversallyOpen f) :
    (over (@AlgebraicGeometry.UniversallyOpen : MorphismProperty Scheme.{u})).presheaf f :=
  sorry

/-- For a representable morphism, Section 67.3 universal openness is equivalent
to every algebraic-space base change, expressed by an `IsPullback` square, being
an open morphism. -/
theorem universallyOpen_presheaf_iff_isOpen_of_isPullback
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.UniversallyOpen : MorphismProperty Scheme.{u})).presheaf f ↔
      ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX g f → Open pZ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
