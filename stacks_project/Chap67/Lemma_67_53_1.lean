module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

/-!
# Representable universal homeomorphisms of algebraic spaces

A representable morphism of algebraic spaces is a universal homeomorphism in the
sense of Section 67.3 if and only if every algebraic-space base change induces a
homeomorphism on underlying point spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.53.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is a universal homeomorphism in
the sense of Section 67.3 if and only if for every morphism of algebraic spaces
`Z ⟶ Y` the morphism of topological spaces `|Z ×_Y X| ⟶ |Z|` is a
homeomorphism. -/
@[stacks 05Z4]
theorem universalHomeomorphism_presheaf_iff_universalHomeomorphism
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.UniversalHomeomorphism : MorphismProperty Scheme.{u})).presheaf f ↔
      UniversalHomeomorphism f :=
  sorry

/-- A representable morphism that is a universal homeomorphism in the sense of
Section 67.3 is a universal homeomorphism as a morphism of algebraic spaces. -/
theorem universalHomeomorphism_of_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.UniversalHomeomorphism :
      MorphismProperty Scheme.{u})).presheaf f) :
    UniversalHomeomorphism f :=
  sorry

/-- A representable morphism that is a universal homeomorphism as a morphism of
algebraic spaces is a universal homeomorphism in the sense of Section 67.3. -/
theorem universalHomeomorphism_presheaf_of_universalHomeomorphism
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : UniversalHomeomorphism f) :
    (over (@AlgebraicGeometry.UniversalHomeomorphism : MorphismProperty Scheme.{u})).presheaf f :=
  sorry

/-- For a representable morphism, Section 67.3 universal homeomorphism is equivalent
to every algebraic-space base change, expressed by an `IsPullback` square, being a
homeomorphism on points. -/
theorem universalHomeomorphism_presheaf_iff_pointsIsHomeomorph_of_isPullback
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.UniversalHomeomorphism : MorphismProperty Scheme.{u})).presheaf f ↔
      ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX g f → pointsIsHomeomorph pZ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
