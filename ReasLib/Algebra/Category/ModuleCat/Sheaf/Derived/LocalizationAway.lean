/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.LocalSectionMul
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w z

namespace SheafOfModules.LocalizationAway

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, z}]

/-- The standard derived category of sheaves of modules over a commutative ring sheaf. -/
@[reducible]
noncomputable instance hasDerivedCategory :
    HasDerivedCategory.{max (max (max u v) w) (z + 1)}
      (SheafOfModules.{z} (SheafOfModules.RingedSite.ringSheaf J O)) :=
  HasDerivedCategory.standard _

/-- The unbounded derived category of sheaves of modules over a commutative ring sheaf. -/
abbrev Derived (O : Sheaf J CommRingCat.{w}) :=
  @DerivedCategory.{max (max (max u v) w) (z + 1)}
    (SheafOfModules.{z} (SheafOfModules.RingedSite.ringSheaf J O))
    inferInstance inferInstance (hasDerivedCategory (O := O))

/-- Restriction to a slice site preserves finite limits for sheaves of modules. -/
theorem overPreservesFiniteLimits (U : C) :
    PreservesFiniteLimits
      (overFunctor (SheafOfModules.RingedSite.ringSheaf J O) U) := sorry

/-- Restriction to a slice site preserves finite colimits for sheaves of modules. -/
theorem overPreservesFiniteColimits (U : C) :
    PreservesFiniteColimits
      (overFunctor (SheafOfModules.RingedSite.ringSheaf J O) U) := sorry

/-- Restriction to a slice site, bundled with its exactness data. -/
noncomputable def restrictionExact (U : C) :
    SheafOfModules.{z} (SheafOfModules.RingedSite.ringSheaf J O) ⥤ₑ
      SheafOfModules.{z}
        (SheafOfModules.RingedSite.ringSheaf.{max u v, v, w} (J.over U) (O.over U)) :=
  @ExactFunctor.of _ _ _ _
    (overFunctor (SheafOfModules.RingedSite.ringSheaf J O) U)
    (overPreservesFiniteLimits (O := O) U)
    (overPreservesFiniteColimits (O := O) U)

/-- Multiplication by a local section as a natural endomorphism of slice restriction. -/
noncomputable def sectionActionNatTrans (U : C) (f : O.obj.obj (op U)) :
    overFunctor (SheafOfModules.RingedSite.ringSheaf J O) U ⟶
      overFunctor (SheafOfModules.RingedSite.ringSheaf J O) U where
  app M := SheafOfModules.sectionActionHom O M U f
  naturality _ _ g := (SheafOfModules.sectionActionHom_naturality O g U f).symm

/-- Multiplication by a local section on the derived restriction of a sheaf module. -/
noncomputable def sectionAction
    (K : Derived.{u, v, w, z} O)
    (U : C) (f : O.obj.obj (op U)) :
    End ((restrictionExact (O := O) U).mapDerivedCategory.obj K) :=
  let α : restrictionExact (O := O) U ⟶ restrictionExact (O := O) U :=
    ObjectProperty.homMk (P := exactFunctor _ _)
      (sectionActionNatTrans (O := O) U f)
  (ExactFunctor.MapDerivedCategory.map α).app K

/-- The multiplication tower with constant derived restriction stages. -/
abbrev tower
    (K : Derived.{u, v, w, z} O)
    (U : C) (f : O.obj.obj (op U)) :
    SequentialInverseSystem
      (Derived.{max u v, v, w, z} (O.over U)) :=
  Functor.ofOpSequence (X := fun _ ↦
    (restrictionExact (O := O) U).mapDerivedCategory.obj K)
    (fun _ ↦ sectionAction K U f)

end SheafOfModules.LocalizationAway
