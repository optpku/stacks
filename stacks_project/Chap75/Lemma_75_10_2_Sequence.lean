/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Exact
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap75.Lemma_75_10_1_Sequence
public import stacks_project.Chap75.Lemma_75_3_1_Comparison
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.MayerVietoris.Pushforward

/-! # Mayer–Vietoris comparison maps for étale pushforward

The shared pushforward owners supply the module, cochain, and derived comparisons.
The source imports preserve the transitive interface used by the relative and
cohomological Mayer–Vietoris constructions.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open ComplexShape

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisPushforwardShortComplex :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (F : X.Modules),
    ShortComplex X.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisPushforwardιDerived :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (E : ModuleDerived X),
    E ⟶ biprod ((pushforwardDerived j).obj ((restrictFunctorDerived j).obj E))
      ((pushforwardDerived f).obj ((restrictFunctorDerived f).obj E)))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisPushforwardπDerived :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f] (E : ModuleDerived X),
    biprod ((pushforwardDerived j).obj ((restrictFunctorDerived j).obj E))
      ((pushforwardDerived f).obj ((restrictFunctorDerived f).obj E)) ⟶
      (pushforwardDerived (fiberHom j f)).obj
        ((restrictFunctorDerived (fiberHom j f)).obj E))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisPushforwardδCochain :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f],
    (restrictFunctor (fiberHom j f) ⋙ pushforward (fiberHom j f)).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X) ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X) ⋙
        shiftFunctor (ModuleDerived X) (1 : ℤ))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mayerVietorisPushforwardTriangle_eq_triangleOfSES :
  ∀ {S : Scheme.{u}} {U V X : AlgebraicSpace S}
    (j : U ⟶ X) [Etale j] (f : V ⟶ X) [Etale f]
    [IsElementaryDistinguishedSquare j f]
    (K : CochainComplex X.Modules ℤ) [K.IsKInjective] [∀ n, Injective (K.X n)]
    (h : (mayerVietorisPushforwardCochainShortComplex j f K).ShortExact),
    mayerVietorisPushforwardTriangle j f (DerivedCategory.Q.obj K) ≅
      DerivedCategory.triangleOfSES h)
