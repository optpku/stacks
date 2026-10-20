/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.Algebra.Category.ModuleCat.Sheaf.TrivSqZeroExt.Splitting

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.TrivSqZeroExt

universe u v w

/- 91.10.5.1 After identifying underlying topoi, a trivialization of a first-order thickening
of ringed topoi splits the structure sheaf as the base sheaf plus its square-zero kernel ideal. -/
@[stacks 08MH] #check (SheafOfModules.RingedSite.TrivSqZeroExt.splittingIso :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {O O' : Sheaf J CommRingCat.{w}} (proj : O' ⟶ O) (s : O ⟶ O')
    (hs : s ≫ proj = 𝟙 O) (hI : KernelIdeal.IsSquareZero proj),
    O' ≅ trivSqZeroExt O (KernelIdeal.restrict proj s))

#check (SheafOfModules.RingedSite.TrivSqZeroExt.splittingHom_comp_fst :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {O O' : Sheaf J CommRingCat.{w}} (proj : O' ⟶ O) (s : O ⟶ O')
    (hs : s ≫ proj = 𝟙 O) (hI : KernelIdeal.IsSquareZero proj),
    (splittingIso proj s hs hI).hom ≫ fst O (KernelIdeal.restrict proj s) = proj)
