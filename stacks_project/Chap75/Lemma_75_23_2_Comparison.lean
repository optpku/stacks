/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal
public import stacks_project.Chap75.Lemma_75_23_1_Comparison

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom.ClosedPresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ProjectionFormula.Ext

/-! # Compatibility for derived Hom in a chosen closed presentation -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed CategoryTheory.Limits ComplexShape

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.extTarget :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] (f : X ⟶ B)
    (H : MonoidalClosed (ModuleDerived X)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (F : Modules B), ModuleDerived X)

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.extTarget_eq :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] (f : X ⟶ B)
    (H : MonoidalClosed (ModuleDerived X)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (F : Modules B),
    extTarget f H E G F =
      (ihomOf H E).obj (DerivedCategory.Q.obj (complexTensorPullback f G F)))

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.localizationMonoidal :
  ∀ {S : Scheme.{u}} (Y : AlgebraicSpace S)
    [MonoidalCategory (ModuleDerived Y)], Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.extTargetMap :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] (f : X ⟶ B)
    (H : MonoidalClosed (ModuleDerived X)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) {F F' : Modules B} (φ : F ⟶ F'),
    extTarget f H E G F ⟶ extTarget f H E G F')

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.ihomOf_commShift :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) [(tensorLeft E).CommShift ℤ], (ihomOf H E).CommShift ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.extTargetδ :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] (f : X ⟶ B)
    (H : MonoidalClosed (ModuleDerived X)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (s : ShortComplex (Modules B))
    (hs : (complexTensorPullbackShortComplex f G s).ShortExact) (i : ℤ)
    [(tensorLeft E).CommShift ℤ],
    cohomologyAb X (extTarget f H E G s.X₃) i ⟶
      cohomologyAb X (extTarget f H E G s.X₁) (i + 1))
