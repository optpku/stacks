module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap67.Definition_67_14_4_IdealSubobject
public import stacks_project.Chap69.Lemma_69_12_8_ClosedImmersion
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Basic

/-! Compatibility checks for the shared coherent-formal-module API. -/
@[expose] public section
open CategoryTheory Opposite CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
noncomputable section
universe u

#check (AlgebraicGeometry.AlgebraicSpace.inducedQuotient :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (F : SequentialInverseSystem (Coh X)) (n : ℕ),
    ((idealPowerProductSubobject I (F.obj (op (n + 1))).obj n).arrow ≫
      (F.stepMap n).hom = 0) →
      ((cokernel (idealPowerProductSubobject I (F.obj (op (n + 1))).obj n).arrow : X.Modules) ⟶
        ((F.obj (op n)).obj : X.Modules)))

#check (AlgebraicGeometry.AlgebraicSpace.stepMap_comp_idealPower_eq_zero :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (F : SequentialInverseSystem (Coh X)) (n : ℕ),
    idealPowerProductSubobject I (F.obj (op n)).obj n = ⊥ →
      (idealPowerProductSubobject I (F.obj (op (n + 1))).obj n).arrow ≫
        (F.stepMap n).hom = 0)

#check (AlgebraicGeometry.AlgebraicSpace.IsCoherentFormalModuleSystem :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X), ObjectProperty (SequentialInverseSystem (Coh X)))

#check (AlgebraicGeometry.AlgebraicSpace.CoherentFormalModules :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (I : IdealSubobject X), Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.isCoherentFormalModuleSystem_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)
    (F : SequentialInverseSystem (Coh X)),
    IsCoherentFormalModuleSystem I F ↔
      (∀ n : ℕ, idealPowerProductSubobject I (F.obj (op n)).obj n = ⊥) ∧
        ∀ n : ℕ,
          ∃ h : (idealPowerProductSubobject I (F.obj (op (n + 1))).obj n).arrow ≫
              (F.stepMap n).hom = 0,
            IsIso (inducedQuotient I F n h))
