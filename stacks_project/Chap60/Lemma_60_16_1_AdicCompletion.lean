/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Cosimplicial.AdicCompletion

@[expose] public section

open CategoryTheory

universe u

/- Degreewise ideal-adic completion of cosimplicial modules, viewed additively. -/
#check (adicCompletion : ∀ {A : CosimplicialObject CommRingCat.{u}}
  (I : CosimplicialIdeal A) (K : PresheafOfModules.{u} (moduleRingPresheaf A)),
  CosimplicialObject Ab)

/- Degreewise completion of a cosimplicial module morphism, viewed additively. -/
#check (adicCompletionMap : ∀ {A : CosimplicialObject CommRingCat.{u}}
  {K M : PresheafOfModules.{u} (moduleRingPresheaf A)} (I : CosimplicialIdeal A)
  (φ : K ⟶ M), adicCompletion I K ⟶ adicCompletion I M)
