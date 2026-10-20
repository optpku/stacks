/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.RepresentablePresheaf.Over
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable

/-!
# Sheafified representables on slice sites

This leaf specializes the terminal identity object of a slice category to its
sheafified representable, without assuming any representable-localization
equivalence.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe w u v

namespace CategoryTheory.GrothendieckTopology.SheafifiedRepresentable.Over

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The sheafified representable of `Over.mk (𝟙 U)` is terminal on the slice site at `U`. -/
noncomputable def mkIdIsoTerminal
    (U : C) [HasWeakSheafify (J.over U) (Type (max w u v))] :
    (J.over U).uliftSheafifiedRepresentable.{w} (Over.mk (𝟙 U)) ≅
      Sheaf.terminal (J.over U) Types.isTerminalPUnit :=
  Functor.mapIso (presheafToSheaf (J.over U) (Type (max w u v)))
    (CategoryTheory.Over.Yoneda.mkIdIsoTerminal.{w} U) ≪≫
      (sheafificationIso (Sheaf.terminal (J.over U) Types.isTerminalPUnit)).symm

/-- The sheafified representable of `Over.mk (𝟙 U)` is a terminal object of the slice sheaf
category. -/
noncomputable def mkIdIsTerminal
    (U : C) [HasWeakSheafify (J.over U) (Type (max w u v))] :
    IsTerminal ((J.over U).uliftSheafifiedRepresentable.{w} (Over.mk (𝟙 U))) :=
  IsTerminal.ofIso
    (Sheaf.isTerminalTerminal (J.over U) Types.isTerminalPUnit)
    (mkIdIsoTerminal J U).symm

end CategoryTheory.GrothendieckTopology.SheafifiedRepresentable.Over
