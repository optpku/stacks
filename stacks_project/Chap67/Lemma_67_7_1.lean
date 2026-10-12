/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Submersive
public import stacks_project.Chap67.Lemma_67_7_1_Quotient

/-!
# Representable universally submersive morphisms of algebraic spaces

A representable morphism of algebraic spaces is universally submersive in the
sense of Section 67.3 if and only if every algebraic-space base change induces a
quotient map on underlying point spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.7.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is universally submersive in the
sense of Section 67.3 if and only if for every morphism of algebraic spaces
`Z ⟶ Y` the morphism of topological spaces given by `Points.map` of a base
change `pZ` in an `IsPullback pZ pX g f` square is a `Topology.IsQuotientMap`. -/
@[stacks 0CFQ]
theorem universallySubmersive_presheaf_iff_universally_pointsIsQuotientMap
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.UniversallySubmersive : MorphismProperty Scheme.{u})).presheaf f ↔
      universally pointsIsQuotientMap f :=
  sorry

/-- A representable morphism that is universally submersive in the sense of
Section 67.3 is universally a quotient map on points. -/
theorem universally_pointsIsQuotientMap_of_universallySubmersive_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.UniversallySubmersive :
      MorphismProperty Scheme.{u})).presheaf f) :
    universally pointsIsQuotientMap f :=
  sorry

/-- A representable morphism that is universally a quotient map on points is
universally submersive in the sense of Section 67.3. -/
theorem universallySubmersive_presheaf_of_universally_pointsIsQuotientMap
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : universally pointsIsQuotientMap f) :
    (over (@AlgebraicGeometry.UniversallySubmersive : MorphismProperty Scheme.{u})).presheaf f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
