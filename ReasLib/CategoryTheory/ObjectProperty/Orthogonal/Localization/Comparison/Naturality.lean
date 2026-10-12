/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Local.Comparison.Naturality
public import ReasLib.CategoryTheory.ObjectProperty.Orthogonal.Localization.Comparison

/-!
# Naturality of Comparisons Between Orthogonal Models

This file specializes local and colocal comparison naturality to right- and left-orthogonal
models for the triangulated localization system `P.trW`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {P : ObjectProperty C} [P.IsTriangulated]

namespace rightOrthogonal.comparisonIso

/-- Right-orthogonal extensions are natural under simultaneous replacement of their source and
target models. -/
@[reassoc, stacks 0A8E "naturality of comparison maps between right-orthogonal models"]
theorem naturality {S T Y Y' Z Z' : C}
    {f : S ⟶ Y} {f' : S ⟶ Y'} {g : T ⟶ Z} {g' : T ⟶ Z'}
    (hf : P.trW f) (hf' : P.trW f') (hg : P.trW g) (hg' : P.trW g')
    (hY : P.rightOrthogonal Y) (hY' : P.rightOrthogonal Y')
    (hZ : P.rightOrthogonal Z) (hZ' : P.rightOrthogonal Z') (u : S ⟶ T) :
    (rightOrthogonal.comparisonIso hf hf' hY hY').hom ≫
        rightOrthogonal.extension hf' hZ' (u ≫ g') =
      rightOrthogonal.extension hf hZ (u ≫ g) ≫
        (rightOrthogonal.comparisonIso hg hg' hZ hZ').hom := sorry

/-- Replacing only the source right-orthogonal model acts by precomposition with its canonical
comparison. -/
@[reassoc (attr := simp)]
theorem changeSource {S T Y Y' Z : C}
    {f : S ⟶ Y} {f' : S ⟶ Y'} {g : T ⟶ Z}
    (hf : P.trW f) (hf' : P.trW f') (hg : P.trW g)
    (hY : P.rightOrthogonal Y) (hY' : P.rightOrthogonal Y')
    (hZ : P.rightOrthogonal Z) (u : S ⟶ T) :
    (rightOrthogonal.comparisonIso hf hf' hY hY').hom ≫
        rightOrthogonal.extension hf' hZ (u ≫ g) =
      rightOrthogonal.extension hf hZ (u ≫ g) := sorry

/-- Replacing only the target right-orthogonal model acts by postcomposition with its canonical
comparison. -/
@[reassoc (attr := simp)]
theorem changeTarget {S T Y Z Z' : C}
    {f : S ⟶ Y} {g : T ⟶ Z} {g' : T ⟶ Z'}
    (hf : P.trW f) (hg : P.trW g) (hg' : P.trW g')
    (hY : P.rightOrthogonal Y) (hZ : P.rightOrthogonal Z)
    (hZ' : P.rightOrthogonal Z') (u : S ⟶ T) :
    rightOrthogonal.extension hf hZ (u ≫ g) ≫
        (rightOrthogonal.comparisonIso hg hg' hZ hZ').hom =
      rightOrthogonal.extension hf hZ' (u ≫ g') := sorry

end rightOrthogonal.comparisonIso

namespace leftOrthogonal.comparisonIso

/-- Left-orthogonal lifts are natural under simultaneous replacement of their source and target
models. -/
@[reassoc, stacks 0A8E "naturality of comparison maps between left-orthogonal models"]
theorem naturality {S T X X' Y Y' : C}
    {f : X ⟶ S} {f' : X' ⟶ S} {g : Y ⟶ T} {g' : Y' ⟶ T}
    (hf : P.trW f) (hf' : P.trW f') (hg : P.trW g) (hg' : P.trW g')
    (hX : P.leftOrthogonal X) (hX' : P.leftOrthogonal X')
    (hY : P.leftOrthogonal Y) (hY' : P.leftOrthogonal Y') (u : S ⟶ T) :
    (leftOrthogonal.comparisonIso hf hf' hX hX').hom ≫
        leftOrthogonal.lift hg' hX' (f' ≫ u) =
      leftOrthogonal.lift hg hX (f ≫ u) ≫
        (leftOrthogonal.comparisonIso hg hg' hY hY').hom := sorry

/-- Replacing only the source left-orthogonal model acts by precomposition with its canonical
comparison. -/
@[reassoc (attr := simp)]
theorem changeSource {S T X X' Y : C}
    {f : X ⟶ S} {f' : X' ⟶ S} {g : Y ⟶ T}
    (hf : P.trW f) (hf' : P.trW f') (hg : P.trW g)
    (hX : P.leftOrthogonal X) (hX' : P.leftOrthogonal X')
    (hY : P.leftOrthogonal Y) (u : S ⟶ T) :
    (leftOrthogonal.comparisonIso hf hf' hX hX').hom ≫
        leftOrthogonal.lift hg hX' (f' ≫ u) =
      leftOrthogonal.lift hg hX (f ≫ u) := sorry

/-- Replacing only the target left-orthogonal model acts by postcomposition with its canonical
comparison. -/
@[reassoc (attr := simp)]
theorem changeTarget {S T X Y Y' : C}
    {f : X ⟶ S} {g : Y ⟶ T} {g' : Y' ⟶ T}
    (hf : P.trW f) (hg : P.trW g) (hg' : P.trW g')
    (hX : P.leftOrthogonal X) (hY : P.leftOrthogonal Y)
    (hY' : P.leftOrthogonal Y') (u : S ⟶ T) :
    leftOrthogonal.lift hg hX (f ≫ u) ≫
        (leftOrthogonal.comparisonIso hg hg' hY hY').hom =
      leftOrthogonal.lift hg' hX (f ≫ u) := sorry

end leftOrthogonal.comparisonIso

end CategoryTheory.ObjectProperty
