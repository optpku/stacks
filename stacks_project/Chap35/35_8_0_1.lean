/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.PullbackSections
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable (S : Scheme.{u}) (ℱ : S.Modules) [ℱ.IsQuasicoherent]

/- 35.8.0.1: for a scheme `S` and a quasi-coherent `𝒪_S`-module `ℱ`, this is the
presheaf `(Over S)ᵒᵖ ⥤ AddCommGrpCat` sending `f : T ⟶ S` to the global sections
of `f^*ℱ`. -/
@[stacks 03DS] #check
  (AlgebraicGeometry.Scheme.Modules.PullbackSections.over S ℱ :
    (CategoryTheory.Over S)ᵒᵖ ⥤ AddCommGrpCat.{u})
