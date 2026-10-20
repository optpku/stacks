/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Support.WeakSerre
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Closure
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.ClosedSubset.Coproduct

@[expose] public section

universe u

#check (SheafOfModules.supportedOn_isWeakSerreClass :
  ∀ {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u}) (T : Set X),
    CategoryTheory.ObjectProperty.IsWeakSerreClass
      (SheafOfModules.supportedOn (𝒪 := 𝒪) T))

#check (AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn.quasiCoherentOnSupportIsTriangulated :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (T : TopologicalSpace.Closeds X),
    (AlgebraicGeometry.Scheme.DerivedQCoh.quasiCoherentOnSupport X T).IsTriangulated)

#check (AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn.hasCoproducts :
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (T : TopologicalSpace.Closeds X),
    CategoryTheory.Limits.HasCoproducts.{u}
      (AlgebraicGeometry.Scheme.DerivedQCoh.SupportedOn X T))
