/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Tensor
public import ReasLib.RingTheory.Coherent.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sectionwise flatness of constant module sheaves

This file records sectionwise flatness as a reusable property of
`ModuleCat`-valued sheaves and proves it for constant sheaves over coherent
rings.  The sectionwise predicate is also the natural input for inverse-limit
constructions of constant quotient sheaves.
-/

@[expose] public section

open Opposite

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Type w} [CommRing R]

/-- A sheaf of `R`-modules is sectionwise flat when its module of sections at
every object of the site is flat over `R`. -/
def SectionwiseFlat (F : Sheaf J (ModuleCat.{w} R)) : Prop :=
  ∀ U : C, Module.Flat R (F.obj.obj (op U))

/-- Unfolding sectionwise flatness at an object of the site. -/
theorem sectionwiseFlat_iff (F : Sheaf J (ModuleCat.{w} R)) :
    F.SectionwiseFlat ↔ ∀ U : C, Module.Flat R (F.obj.obj (op U)) := sorry

/-- Lemma 18.42.3 (093L): over a coherent ring, the constant sheaf of a flat
module is sectionwise flat. -/
@[stacks 093L]
theorem constant_sectionwiseFlat
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]
    [IsCoherentRing R] (M : ModuleCat.{w} R) [Module.Flat R M] :
    ((constantSheaf J (ModuleCat.{w} R)).obj M).SectionwiseFlat := sorry

/-- At each object of the site, sections of the constant sheaf of a flat
module over a coherent ring are flat. -/
theorem constant_app_flat
    (J : GrothendieckTopology C) [HasWeakSheafify J (ModuleCat.{w} R)]
    [IsCoherentRing R] (M : ModuleCat.{w} R) [Module.Flat R M] (U : C) :
    Module.Flat R (((constantSheaf J (ModuleCat.{w} R)).obj M).obj.obj (op U)) := sorry

end CategoryTheory.Sheaf
