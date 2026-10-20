/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Support

/-!
# Derived quasi-coherent modules supported on a subset

`DerivedQCoh.SupportedOn X T` is the full subcategory of `D(𝒪_X)` on complexes
with quasi-coherent cohomology supported on `T ⊆ Points X`.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

variable {S : Scheme.{u}}

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.quasiCoherentSupportedOn :
  ∀ (X : AlgebraicSpace S), Set (Points X) → ObjectProperty (ModuleDerived X))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn :
  ∀ (X : AlgebraicSpace S), Set (Points X) → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.mem_iff :
  ∀ {X : AlgebraicSpace S} {T : Set (Points X)} (E : ModuleDerived X),
    DerivedQCoh.quasiCoherentSupportedOn X T E ↔
      derivedQuasiCoherentModuleProperty X E ∧ ModuleDerived.IsSupportedOn E T)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.inclusion :
  ∀ (X : AlgebraicSpace S) (T : Set (Points X)),
    DerivedQCoh.SupportedOn X T ⥤ DerivedQCoh X)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.inclusion_obj_obj :
  ∀ {X : AlgebraicSpace S} {T : Set (Points X)} (K : DerivedQCoh.SupportedOn X T),
    ((DerivedQCoh.SupportedOn.inclusion X T).obj K).obj = K.obj)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.mk :
  ∀ {X : AlgebraicSpace S} {T : Set (Points X)} (E : DerivedQCoh X),
    ModuleDerived.IsSupportedOn E.obj T → DerivedQCoh.SupportedOn X T)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.obj_properties :
  ∀ {X : AlgebraicSpace S} {T : Set (Points X)} (K : DerivedQCoh.SupportedOn X T),
    derivedQuasiCoherentModuleProperty X K.obj ∧ ModuleDerived.IsSupportedOn K.obj T)
