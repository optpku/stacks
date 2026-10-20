/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap96.Definition_96_11_1_QCoh
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver

universe u

/- Definition 96.11.1: let `p : 𝒳 ⟶ (Sch/S)_fppf` be a category fibred in
groupoids. A quasi-coherent module on `𝒳`, or a quasi-coherent `𝒪_𝒳`-module,
is a quasi-coherent module on the ringed site `(𝒳_fppf, 𝒪_𝒳)` as in
Modules on Sites, Definition 18.23.1. -/
@[stacks 06WG] #check
  (AlgebraicGeometry.GroupoidsOver.quasiCoherentModuleProperty :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
      CategoryTheory.ObjectProperty (RingedSite.ModuleCat.{u} (fppfRingedSite X)))

/- The category of quasi-coherent sheaves on `𝒳` is denoted `QCoh(𝒪_𝒳)`. -/
#check (AlgebraicGeometry.GroupoidsOver.QCoh :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S), Type (u + 1))

/- The forgetful inclusion `QCoh(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)`. -/
#check (AlgebraicGeometry.GroupoidsOver.QCoh.inclusion :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    QCoh X ⥤ RingedSite.ModuleCat.{u} (fppfRingedSite X))
