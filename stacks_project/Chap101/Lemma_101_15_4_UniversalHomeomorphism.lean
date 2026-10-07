module

public import stacks_project.Chap101.Definition_101_15_2_UniversalHomeomorphism
public import stacks_project.Chap101.Lemma_101_15_1

/-!
# Composition of universal homeomorphisms of algebraic stacks

Companion API for the existing `UniversalHomeomorphism` class: a constructor
from the 2-fibre-product field, composition of point-space homeomorphisms, and
the chosen-product characterization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversalHomeomorphism

/-- A morphism is a universal homeomorphism as soon as every 2-fibre-product
base change induces a homeomorphism on points. -/
theorem of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : ∀ {Z P : GroupoidsOver S} [AlgebraicStack Z] [AlgebraicStack P]
      {g : Z ⟶ Y} {fst : P ⟶ X} {snd : P ⟶ Z} (iso : fst ≫ f ≅ snd ≫ g),
      (Points.cone iso).IsBilimit → pointsIsHomeomorph snd) :
    UniversalHomeomorphism f :=
  sorry

end UniversalHomeomorphism

/-- Composition of morphisms that induce homeomorphisms on canonical point
spaces again induces a homeomorphism on canonical point spaces. -/
theorem pointsIsHomeomorph_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z] {f : X ⟶ Y}
    {g : Y ⟶ Z} (hf : pointsIsHomeomorph f) (hg : pointsIsHomeomorph g) :
    pointsIsHomeomorph (f ≫ g) :=
  sorry

/-- A morphism of algebraic stacks is a universal homeomorphism if and only if
every chosen 2-fibre-product projection `Z ×_Y X ⟶ Z` induces a homeomorphism
on points. -/
theorem universalHomeomorphism_iff_isHomeomorphAfterBaseChange
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    UniversalHomeomorphism f ↔ Groupoids.Hom.isHomeomorphAfterBaseChange f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
