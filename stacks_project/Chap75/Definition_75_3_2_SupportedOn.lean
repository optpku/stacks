/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Support
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap67.Lemma_67_31_6_ModuleSupport

/-!
# Derived modules supported on a subset

A derived `𝒪_X`-module is supported on a subset `T ⊆ Points X` when every
cohomology sheaf is supported on `T`. This is the algebraic-space specialization of
`DerivedCategory.cohomologyIn`.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

#check (AlgebraicGeometry.AlgebraicSpace.Modules.moduleSupportedOn :
  Set (Points X) → ObjectProperty X.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_moduleSupportedOn_iff :
  ∀ (T : Set (Points X)) (F : X.Modules),
    Modules.moduleSupportedOn T F ↔ Modules.moduleSupport F ⊆ T)

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.supportedOn :
  Set (Points X) → ObjectProperty (ModuleDerived X))

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsSupportedOn :
  ModuleDerived X → Set (Points X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.SupportedOn :
  Set (Points X) → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.SupportedOn.inclusion :
  ∀ T : Set (Points X), ModuleDerived.SupportedOn T ⥤ ModuleDerived X)

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.isSupportedOn_iff :
  ∀ (K : ModuleDerived X) (T : Set (Points X)),
    ModuleDerived.IsSupportedOn K T ↔
      ∀ i : ℤ, Modules.moduleSupportedOn T
        ((DerivedCategory.homologyFunctor (Modules X) i).obj K))
