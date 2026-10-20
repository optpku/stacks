/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Local.Comparison

/-!
# Naturality of Canonical Comparisons of Local and Colocal Models

Canonical extensions and lifts do not depend on a chosen local or colocal model.  This file
records the two-sided naturality square and the source-only and target-only simplification API.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}

namespace isLocal.comparisonIso

/-- Canonical extensions are natural under simultaneous replacement of their local source and
target models. -/
@[reassoc, stacks 0A8E "naturality of comparison maps between local models"]
theorem naturality {S T Y Y' Z Z' : C}
    {f : S ⟶ Y} {f' : S ⟶ Y'} {g : T ⟶ Z} {g' : T ⟶ Z'}
    (hf : W f) (hf' : W f') (hg : W g) (hg' : W g')
    (hY : W.isLocal Y) (hY' : W.isLocal Y')
    (hZ : W.isLocal Z) (hZ' : W.isLocal Z') (u : S ⟶ T) :
    (isLocal.comparisonIso hf hf' hY hY').hom ≫
        isLocal.extension hf' hZ' (u ≫ g') =
      isLocal.extension hf hZ (u ≫ g) ≫
        (isLocal.comparisonIso hg hg' hZ hZ').hom := sorry

/-- Replacing only the source local model acts by precomposition with its canonical
comparison. -/
@[reassoc (attr := simp)]
theorem changeSource {S T Y Y' Z : C}
    {f : S ⟶ Y} {f' : S ⟶ Y'} {g : T ⟶ Z}
    (hf : W f) (hf' : W f') (hg : W g)
    (hY : W.isLocal Y) (hY' : W.isLocal Y')
    (hZ : W.isLocal Z) (u : S ⟶ T) :
    (isLocal.comparisonIso hf hf' hY hY').hom ≫
        isLocal.extension hf' hZ (u ≫ g) =
      isLocal.extension hf hZ (u ≫ g) := sorry

/-- Replacing only the target local model acts by postcomposition with its canonical
comparison. -/
@[reassoc (attr := simp)]
theorem changeTarget {S T Y Z Z' : C}
    {f : S ⟶ Y} {g : T ⟶ Z} {g' : T ⟶ Z'}
    (hf : W f) (hg : W g) (hg' : W g')
    (hY : W.isLocal Y) (hZ : W.isLocal Z)
    (hZ' : W.isLocal Z') (u : S ⟶ T) :
    isLocal.extension hf hZ (u ≫ g) ≫
        (isLocal.comparisonIso hg hg' hZ hZ').hom =
      isLocal.extension hf hZ' (u ≫ g') := sorry

end isLocal.comparisonIso

namespace isColocal.comparisonIso

/-- Canonical lifts are natural under simultaneous replacement of their colocal source and
target models. -/
@[reassoc, stacks 0A8E "naturality of comparison maps between colocal models"]
theorem naturality {S T X X' Y Y' : C}
    {f : X ⟶ S} {f' : X' ⟶ S} {g : Y ⟶ T} {g' : Y' ⟶ T}
    (hf : W f) (hf' : W f') (hg : W g) (hg' : W g')
    (hX : W.isColocal X) (hX' : W.isColocal X')
    (hY : W.isColocal Y) (hY' : W.isColocal Y') (u : S ⟶ T) :
    (isColocal.comparisonIso hf hf' hX hX').hom ≫
        isColocal.lift hg' hX' (f' ≫ u) =
      isColocal.lift hg hX (f ≫ u) ≫
        (isColocal.comparisonIso hg hg' hY hY').hom := sorry

/-- Replacing only the source colocal model acts by precomposition with its canonical
comparison. -/
@[reassoc (attr := simp)]
theorem changeSource {S T X X' Y : C}
    {f : X ⟶ S} {f' : X' ⟶ S} {g : Y ⟶ T}
    (hf : W f) (hf' : W f') (hg : W g)
    (hX : W.isColocal X) (hX' : W.isColocal X')
    (hY : W.isColocal Y) (u : S ⟶ T) :
    (isColocal.comparisonIso hf hf' hX hX').hom ≫
        isColocal.lift hg hX' (f' ≫ u) =
      isColocal.lift hg hX (f ≫ u) := sorry

/-- Replacing only the target colocal model acts by postcomposition with its canonical
comparison. -/
@[reassoc (attr := simp)]
theorem changeTarget {S T X Y Y' : C}
    {f : X ⟶ S} {g : Y ⟶ T} {g' : Y' ⟶ T}
    (hf : W f) (hg : W g) (hg' : W g')
    (hX : W.isColocal X) (hY : W.isColocal Y)
    (hY' : W.isColocal Y') (u : S ⟶ T) :
    isColocal.lift hg hX (f ≫ u) ≫
        (isColocal.comparisonIso hg hg' hY hY').hom =
      isColocal.lift hg' hX (f ≫ u) := sorry

end isColocal.comparisonIso

end CategoryTheory.MorphismProperty
