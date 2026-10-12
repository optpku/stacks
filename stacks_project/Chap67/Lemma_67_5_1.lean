/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap67.Definition_67_5_2_Surjective

/-!
# Representable surjective morphisms of algebraic spaces

A representable morphism of algebraic spaces is surjective in the
sense of Section 67.3 if and only if the induced map of associated
point spaces is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.5.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is surjective in the
sense of Section 67.3 if and only if `|f| : |X| ⟶ |Y|` is surjective. -/
@[stacks 03MD]
theorem surjective_presheaf_iff_map_surjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u})).presheaf f ↔
      Function.Surjective (Points.map f) :=
  sorry

/-- For a representable morphism of algebraic spaces, Section 67.3
surjectivity is equivalent to algebraic-space surjectivity. -/
theorem surjective_presheaf_iff_surjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u})).presheaf f ↔
      Surjective f :=
  sorry

/-- A representable morphism that is surjective in the sense of
Section 67.3 is surjective as a morphism of algebraic spaces. -/
theorem surjective_of_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.Surjective :
      MorphismProperty Scheme.{u})).presheaf f) :
    Surjective f :=
  sorry

/-- A representable morphism that is surjective as a morphism of
algebraic spaces is surjective in the sense of Section 67.3. -/
theorem surjective_presheaf_of_surjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : Surjective f) :
    (over (@AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u})).presheaf f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
