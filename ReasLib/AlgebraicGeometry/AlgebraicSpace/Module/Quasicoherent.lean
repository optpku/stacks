/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Basic

/-!
# Quasi-coherent modules on an algebraic space

A quasi-coherent `𝒪_X`-module is a quasi-coherent module sheaf on the small étale ringed
site of `X`. The category of such sheaves is the full subcategory `QCoh 𝒪_X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

/-- The structure sheaf of an algebraic space, viewed as a module over itself, is
quasi-coherent. -/
instance instIsQuasicoherentUnit {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (SheafOfModules.unit (structureSheaf X) : X.Modules).IsQuasicoherent :=
  sorry

end Modules

/-- The object property of quasi-coherent module sheaves on the small étale ringed site of an
algebraic space. -/
abbrev quasiCoherentModuleProperty {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ObjectProperty (Modules X) :=
  SheafOfModules.isQuasicoherent (structureSheaf X)

/-- Quasi-coherence on `X` is mathlib's site-level quasi-coherence predicate for `𝒪_X`. -/
theorem quasiCoherentModuleProperty_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    quasiCoherentModuleProperty X = SheafOfModules.isQuasicoherent (structureSheaf X) :=
  rfl

/-- The category of quasi-coherent `𝒪_X`-modules on an algebraic space. -/
abbrev QCoh {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  (quasiCoherentModuleProperty X).FullSubcategory

namespace QCoh

/-- The inclusion of quasi-coherent modules into all module sheaves on `X`. -/
abbrev inclusion {S : Scheme.{u}} (X : AlgebraicSpace S) : QCoh X ⥤ Modules X :=
  (quasiCoherentModuleProperty X).ι

end QCoh

end AlgebraicGeometry.AlgebraicSpace
