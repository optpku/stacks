/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.Exactness
public import stacks_project.Chap96.Definition_96_11_1_QCoh

/-! # Abelian and extension properties of quasi-coherent modules -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.ObjectProperty AlgebraicGeometry.GroupoidsOver

universe u

#check (AlgebraicGeometry.GroupoidsOver.QCoh.instAbelian :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Abelian (QCoh X))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.inclusion_preservesFiniteColimits :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    PreservesFiniteColimits (QCoh.inclusion X))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.closedUnderExtensions :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    (quasiCoherentModuleProperty X).IsClosedUnderExtensions)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.isQuasicoherent_of_shortExact :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {sc : ShortComplex (RingedSite.ModuleCat.{u} (fppfRingedSite X))},
    sc.ShortExact → quasiCoherentModuleProperty X sc.X₁ →
      quasiCoherentModuleProperty X sc.X₃ → quasiCoherentModuleProperty X sc.X₂)
