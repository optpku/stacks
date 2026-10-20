/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CompletionMap
public import stacks_project.Chap52.Definition_52_6_4
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic

@[expose] public section

open CategoryTheory SheafOfModules.RingedSite RingedSite.Hom RingedSite.Hom.ModuleDerived

noncomputable section

universe u v w z

/- The canonical completion-map API is defined in the ReasLib owner above. -/
#check (RingedSite.Hom.ModuleDerived.IsDerivedCompletion :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C},
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] →
    ∀ {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, z}],
      Subobject (unitModule J O) →
        ∀ {K Khat : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O)},
          (K ⟶ Khat) → Prop)
