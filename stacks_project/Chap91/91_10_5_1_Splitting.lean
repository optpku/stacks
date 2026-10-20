/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TrivSqZeroExt.Splitting

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.TrivSqZeroExt

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O O' : Sheaf J CommRingCat.{w}}

#check (splittingHom_comp_fst :
  ∀ (proj : O' ⟶ O) (s : O ⟶ O') (hs : s ≫ proj = 𝟙 O)
    (hI : KernelIdeal.IsSquareZero proj),
    (splittingIso proj s hs hI).hom ≫ fst O (KernelIdeal.restrict proj s) = proj)

#check (SheafOfModules.RingedSite.TrivSqZeroExt.splittingIso :
  ∀ (proj : O' ⟶ O) (s : O ⟶ O') (hs : s ≫ proj = 𝟙 O)
    (hI : KernelIdeal.IsSquareZero proj),
    O' ≅ trivSqZeroExt O (KernelIdeal.restrict proj s))

end SheafOfModules.RingedSite.TrivSqZeroExt
