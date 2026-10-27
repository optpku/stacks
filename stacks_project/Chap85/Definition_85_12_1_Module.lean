/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Cartesian
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import stacks_project.Chap85.Definition_85_12_1_Component

/-!
# Module and derived comparisons on a ringed simplicial site

Restriction of `O`-modules and of objects of `D(O)` and `D(C_total)` to stages,
together with the simplex-operator maps `f_φ^* F_m ⟶ F_n` and `Lf_φ^* K_m ⟶ K_n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor
open RingedSite
open ComplexShape

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [instWeakSheafify : ∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [instLeftKan : ∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [instMorphismDiagram : IsMorphismDiagram C J]
include instMorphismDiagram instWeakSheafify instLeftKan
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/-- Restriction of an object of `D(C_total)` to the degree-`n` site. -/
def derivedComponent (n : SimplexCategory) :
    DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}) ⥤
      DerivedCategory (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}) :=
  derivedRestrict C J n

/-- `derivedComponent n` is `mapDerivedCategory` of abelian stage restriction. -/
theorem derivedComponent_eq (n : SimplexCategory) :
    derivedComponent C J n = (component C J AddCommGrpCat.{w} n).mapDerivedCategory :=
  rfl

end CategoryTheory.SimplicialSites
