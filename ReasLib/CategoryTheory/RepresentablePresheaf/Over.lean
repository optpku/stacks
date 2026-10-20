/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.RepresentablePresheaf
public import Mathlib.CategoryTheory.Sites.Over

/-!
# The Yoneda embedding of a slice category

The identity arrow of `Over U` is terminal.  This leaf records the resulting
terminal representable presheaf independently of any Grothendieck topology.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w u v

namespace CategoryTheory.Over.Yoneda

variable {C : Type u} [Category.{v} C]

/-- The universe-lifted representable presheaf of `Over.mk (𝟙 U)` is terminal on `Over U`. -/
noncomputable def mkIdIsoTerminal (U : C) :
    ((CategoryTheory.uliftYoneda.{max w u v}.obj (Over.mk (𝟙 U))) :
      (Over U)ᵒᵖ ⥤ Type (max w u v)) ≅
        (Functor.const (Over U)ᵒᵖ).obj (PUnit : Type (max w u v)) :=
  let yonedaOver : Over U ⥤ (Over U)ᵒᵖ ⥤ Type (max w u v) :=
    CategoryTheory.uliftYoneda.{max w u v}
  let h_representable :
      IsTerminal
        ((yonedaOver.obj (Over.mk (𝟙 U))) :
          (Over U)ᵒᵖ ⥤ Type (max w u v)) :=
    IsTerminal.isTerminalObj yonedaOver (Over.mk (𝟙 U)) Over.mkIdTerminal
  IsTerminal.uniqueUpToIso h_representable <|
    Functor.isTerminalConst (Over U)ᵒᵖ Types.isTerminalPUnit

end CategoryTheory.Over.Yoneda
