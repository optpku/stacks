/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap66.Proposition_66_32_2_Coherator
public import stacks_project.Chap67.Lemma_67_11_2_Pushforward
public import stacks_project.Chap75.«75_5_1_1_Comparison»
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent

/-! # Derived coherator and quasi-coherent pushforward on algebraic spaces

Typed compatibility checks for the derived functors and their canonical units.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

#check (AlgebraicGeometry.AlgebraicSpace.modulesIsGrothendieckAbelian :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), IsGrothendieckAbelian.{u} (Modules X))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.pushforward.additive :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    (pushforward f).Additive)

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.instIsGrothendieckAbelian :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), IsGrothendieckAbelian.{u} (QCoh X))

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.pushforward.additive :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f],
    (pushforward f).Additive)

end AlgebraicGeometry.AlgebraicSpace.QCoh

namespace AlgebraicGeometry.AlgebraicSpace.QCoh.Derived

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.Derived.coherator :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    ModuleDerived X ⥤ DerivedCategory (QCoh X))

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.Derived.coheratorUnit :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (QCoh.coherator X).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex (QCoh X) ℤ ⥤ DerivedCategory (QCoh X)) ⟶
      (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ DerivedCategory (Modules X)) ⋙
        coherator X)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.Derived.coheratorIsRightDerived :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (coherator X).IsRightDerivedFunctor (coheratorUnit X)
      (HomologicalComplex.quasiIso (Modules X) (up ℤ)))

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.Derived.pushforward :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    DerivedCategory (QCoh X) ⥤ DerivedCategory (QCoh Y))

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.Derived.pushforwardUnit :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f],
    (QCoh.pushforward f).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex (QCoh Y) ℤ ⥤ DerivedCategory (QCoh Y)) ⟶
      (DerivedCategory.Q : CochainComplex (QCoh X) ℤ ⥤ DerivedCategory (QCoh X)) ⋙
        pushforward f)

#check (AlgebraicGeometry.AlgebraicSpace.QCoh.Derived.pushforwardIsRightDerived :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f],
    (pushforward f).IsRightDerivedFunctor (pushforwardUnit f)
      (HomologicalComplex.quasiIso (QCoh X) (up ℤ)))

end AlgebraicGeometry.AlgebraicSpace.QCoh.Derived
