module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap67.Definition_67_9_2_Closed

/-!
# Representable universally closed morphisms of algebraic spaces

A representable morphism of algebraic spaces is universally closed in the
sense of Section 67.3 if and only if every algebraic-space base change induces a
closed map on underlying point spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.9.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is universally closed in the
sense of Section 67.3 if and only if for every morphism of algebraic spaces
`Z ⟶ Y` the morphism of topological spaces `|Z ×_Y X| ⟶ |Z|` is closed. -/
@[stacks 03XD]
theorem universallyClosed_presheaf_iff_universallyClosed
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.UniversallyClosed : MorphismProperty Scheme.{u})).presheaf f ↔
      UniversallyClosed f :=
  sorry

/-- A representable morphism that is universally closed in the sense of
Section 67.3 is universally closed as a morphism of algebraic spaces. -/
theorem universallyClosed_of_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.UniversallyClosed :
      MorphismProperty Scheme.{u})).presheaf f) :
    UniversallyClosed f :=
  sorry

/-- A representable morphism that is universally closed as a morphism of
algebraic spaces is universally closed in the sense of Section 67.3. -/
theorem universallyClosed_presheaf_of_universallyClosed
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : UniversallyClosed f) :
    (over (@AlgebraicGeometry.UniversallyClosed : MorphismProperty Scheme.{u})).presheaf f :=
  sorry

/-- For a representable morphism, Section 67.3 universal closedness is equivalent
to every algebraic-space base change, expressed by an `IsPullback` square, being
a closed morphism. -/
theorem universallyClosed_presheaf_iff_isClosed_of_isPullback
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.UniversallyClosed : MorphismProperty Scheme.{u})).presheaf f ↔
      ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX g f → Closed pZ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
