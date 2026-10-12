/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact

/-!
# Representable quasi-compact morphisms of algebraic spaces

A representable morphism of algebraic spaces is quasi-compact in the
sense of Section 67.3 if and only if every fibre product against a
quasi-compact algebraic space is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.8.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a representable
morphism of algebraic spaces over `S`. Then `f` is quasi-compact in the
sense of Section 67.3 if and only if for every quasi-compact algebraic space
`Z` and any morphism `Z ⟶ Y` the algebraic space `Z ×_Y X` is quasi-compact. -/
@[stacks 03HD]
theorem quasiCompact_presheaf_iff_quasiCompact
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf f ↔
      QuasiCompact f :=
  sorry

/-- A representable morphism that is quasi-compact in the sense of
Section 67.3 is quasi-compact as a morphism of algebraic spaces. -/
theorem quasiCompact_of_presheaf
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : (over (@AlgebraicGeometry.QuasiCompact :
      MorphismProperty Scheme.{u})).presheaf f) :
    QuasiCompact f :=
  sorry

/-- A representable morphism that is quasi-compact as a morphism of
algebraic spaces is quasi-compact in the sense of Section 67.3. -/
theorem quasiCompact_presheaf_of_quasiCompact
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) (h : QuasiCompact f) :
    (over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf f :=
  sorry

/-- For a representable morphism, Section 67.3 quasi-compactness is equivalent
to every fibre product against a quasi-compact algebraic space, expressed by an
`IsPullback` square, being a quasi-compact algebraic space. -/
theorem quasiCompact_presheaf_iff_isQuasiCompact_of_isPullback
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) :
    (over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf f ↔
      ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} {pZ : P ⟶ Z} {pX : P ⟶ X}
        [IsQuasiCompact Z], IsPullback pZ pX g f → IsQuasiCompact P :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
