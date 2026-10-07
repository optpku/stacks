module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Localization.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

/-!
# Derived pullback of modules on ringed spaces

This module owns the homotopy-level inverse-image functor and its unbounded total left derived
functor for morphisms of ringed spaces.
-/

open CategoryTheory
open ComplexShape
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The quasi-isomorphisms used to localize the homotopy category of module sheaves on a ringed
space. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The homotopy-to-derived functor induced by module pullback along a morphism of ringed spaces.
-/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(pullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤
      DerivedCategory (RingedSpace.Modules X) :=
  Functor.Homotopy.toDerived (pullback f)

/-- Module pullback on homotopy categories admits an everywhere defined total left derived functor.
-/
theorem modulePullbackToDerived_hasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)]
    [CategoryWithHomology (RingedSpace.Modules Y)]
    [(pullback f).Additive] :
    (modulePullbackToDerived f).HasLeftDerivedFunctor (ModuleQis Y) := sorry

/-- The canonical total-left-derived-functor instance for module pullback. -/
instance instModulePullbackToDerivedHasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)]
    [CategoryWithHomology (RingedSpace.Modules Y)]
    [(pullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) := sorry

/-- The generic homotopy-to-derived spelling of module pullback admits the same total-left-derived
functor instance.  This bridge lets generic derived-composition APIs apply directly to ringed
spaces. -/
instance instPullbackToDerivedHasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)]
    [CategoryWithHomology (RingedSpace.Modules Y)]
    [(pullback f).Additive] :
    Functor.HasLeftDerivedFunctor
      (Functor.Homotopy.toDerived (pullback f))
      (HomotopyCategory.quasiIso (RingedSpace.Modules Y) (up ℤ)) := sorry

/-- The opens-ringed-site presentation of module pullback has a total-left-derived functor. -/
@[instance]
theorem opensRingedSiteHom_modulePullbackToDerived_hasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)]
    [CategoryWithHomology (RingedSpace.Modules Y)]
    [(pullback f).Additive]
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived (opensRingedSiteHom f))
      (RingedSite.Hom.ModuleQis (opensRingedSite Y)) := sorry

/-- Pullback along a composite of opens-ringed-site morphisms has a total-left-derived functor. -/
theorem opensRingedSiteHom_comp_modulePullbackToDerived_hasLeftDerivedFunctor
    {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [CategoryWithHomology (RingedSpace.Modules X)]
    [CategoryWithHomology (RingedSpace.Modules Y)]
    [CategoryWithHomology (RingedSpace.Modules Z)]
    [(pullback f).Additive] [(pullback g).Additive]
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived
        (RingedSite.Hom.comp (opensRingedSiteHom f) (opensRingedSiteHom g)))
      (RingedSite.Hom.ModuleQis (opensRingedSite Z)) := sorry

/-- The unbounded derived pullback functor `Lf^*` on module sheaves over ringed spaces. -/
noncomputable def modulePullbackDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)]
    [CategoryWithHomology (RingedSpace.Modules Y)]
    [(pullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    DerivedCategory (RingedSpace.Modules Y) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  (modulePullbackToDerived f).totalLeftDerived DerivedCategory.Qh (ModuleQis Y)

namespace modulePullbackDerived

/-- Derived pullback is the total left derived functor of pullback on module sheaves. The canonical
homology, additivity, and derived-functor instances are inferred from the ringed spaces and their
morphism. -/
@[stacks 08DE "derived pullback universal property", instance]
theorem isLeftDerivedFunctor {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (modulePullbackDerived f).IsLeftDerivedFunctor
      ((modulePullbackToDerived f).totalLeftDerivedCounit DerivedCategory.Qh (ModuleQis Y))
      (ModuleQis Y) := sorry

end modulePullbackDerived

end AlgebraicGeometry.RingedSpace

namespace RingedSpaceDerivedPullback

/-- Notation for unbounded derived pullback on modules over a ringed space. -/
scoped notation:max "L(" f ")" "^*" =>
  AlgebraicGeometry.RingedSpace.modulePullbackDerived f

end RingedSpaceDerivedPullback
