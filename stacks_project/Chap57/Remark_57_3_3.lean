/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Triangulated.PeriodicHom
public import stacks_project.Chap57.Remark_57_3_3_Matress
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated ComplexShape HomologicalComplex₂ Limits
  HomologicalComplex₂.Matress

universe v u

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D]

/- Remark 57.3.3. With Mathlib's rotation convention and the source's unsigned
shifted transition maps, the all-indices TR3 law has factor (-1)^(p+q) in its
last equation. This is the sign-corrected translation; at p=q=0 it is ordinary
TR3. The printed all-indices unsigned equation is not valid in this convention. -/
@[stacks 0H8B] #check (HomologicalComplex₂.Matress.fromTriangles :
  ∀ {X Y : Triangle D} (hX : X ∈ distTriang D) (hY : Y ∈ distTriang D),
    HomologicalComplex₂.Matress (HomologicalComplex₂.Matress.complex hX hY)
      (HomologicalComplex₂.Matress.period hX hY))

end
