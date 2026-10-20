/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef

public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable.Pullback
public import Mathlib.CategoryTheory.Sites.Over
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

/- Lemma 7.25.3 (00Y0): localization lower shriek sends the lifted sheafified representable of
an object of `Over U` to the corresponding lifted sheafified representable in the ambient site. -/
section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (U : C)
variable [∀ F : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasLeftKanExtension F]
variable [HasWeakSheafify (J.over U) (Type (max u v))]
variable [HasWeakSheafify J (Type (max u v))]

@[stacks 03HU] #check Functor.SheafifiedRepresentable.pullbackIso (Over.forget U) (J.over U) J

#check Functor.SheafifiedRepresentable.pullbackComparison (Over.forget U) (J.over U) J

end
