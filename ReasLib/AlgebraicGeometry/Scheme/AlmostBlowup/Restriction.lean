/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsAlmostBlowupSquare

/-- For an almost blowup square, containment of the open complement of the exceptional
locus in a finitely presented closed subscheme is equivalent to containment of the
canonical strict transform in that subscheme. -/
theorem openComplement_contained_iff_strictTransform_contained
    {X X' W : Scheme.{u}} (b : X' ⟶ X) (I : X.IdealSheafData)
    (i : W ⟶ X') [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    (hSquare : IsAlmostBlowupSquare b I) :
    i.ker ≤ (I.comap b).openComplement.ι.ker ↔
      i.ker ≤ (strictTransformSnd b (I.comap b) (𝟙 X)).ker := sorry

/-- For an almost blowup square, containment of its canonical strict transform in a
finitely presented closed subscheme is equivalent to the restricted square being an
almost blowup square. -/
theorem strictTransform_contained_iff_restrict
    {X X' W : Scheme.{u}} (b : X' ⟶ X) (I : X.IdealSheafData)
    (i : W ⟶ X') [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    (hSquare : IsAlmostBlowupSquare b I) :
    i.ker ≤ (strictTransformSnd b (I.comap b) (𝟙 X)).ker ↔
      IsAlmostBlowupSquare (i ≫ b) I := sorry

end AlgebraicGeometry.IsAlmostBlowupSquare
