/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic

/-! # Derived category of quasi-coherent modules on an algebraic space

Definition 75.5.1 is the full subcategory of the unbounded derived module category
whose cohomology sheaves are quasi-coherent.
-/

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived :
  {S : AlgebraicGeometry.Scheme.{u}} → AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh :
  {S : AlgebraicGeometry.Scheme.{u}} → AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.inclusion :
  {S : AlgebraicGeometry.Scheme.{u}} → (X : AlgebraicGeometry.AlgebraicSpace S) →
    CategoryTheory.Functor (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh X)
      (AlgebraicGeometry.AlgebraicSpace.ModuleDerived X))
#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.mem_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    (E : AlgebraicGeometry.AlgebraicSpace.ModuleDerived X),
    AlgebraicGeometry.AlgebraicSpace.derivedQuasiCoherentModuleProperty X E ↔
      ∀ n : ℤ, AlgebraicGeometry.AlgebraicSpace.quasiCoherentModuleProperty X
        ((DerivedCategory.homologyFunctor
          (AlgebraicGeometry.AlgebraicSpace.Modules X) n).obj E))
