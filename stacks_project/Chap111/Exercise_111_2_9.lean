/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FilteredColimit.FinitelyGenerated
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
import StacksCheckRecall

@[expose] public section

universe u v

/- Exercise 111.2.9 (1): any module is the directed colimit of its finitely generated
submodules, via the inclusion system `Module.fgSystem` of `{N : Submodule R M // N.FG}`. -/
@[stacks 02CP]
#check (ModuleCat.fgSystemColimitIso :
  ∀ (R : Type u) (M : Type (max u v)) [Ring R] [AddCommGroup M] [Module R M]
    [DecidableEq (Submodule R M)],
    ModuleCat.of R (Module.DirectLimit (fun N : {N : Submodule R M // N.FG} => N.1)
      (Module.fgSystem R M)) ≅ ModuleCat.of R M)

/- Exercise 111.2.9 (2): any module is in some way a filtered colimit of finitely presented
modules, i.e. it lies in `(ModuleCat.isFinitePresentation R).ind`. -/
@[stacks 02CP]
#check (ModuleCat.isFinitePresentation_ind :
  ∀ (R : Type u) [Ring R] (M : ModuleCat.{max u v} R),
    (ModuleCat.isFinitePresentation.{u, max u v} R).ind.{max u v} M)
