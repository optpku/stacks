/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.SerreFunctor.Structure
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A fixed endofunctor is a Serre functor when it is linear and an equivalence, all Hom spaces
are finite-dimensional, and one family of linear Hom-duality equivalences is natural in both
variables. -/
def IsSerre (k : Type w) [Field k] [CategoryTheory.Linear k C] (F : C ⥤ C) : Prop :=
  (∀ X Y : C, FiniteDimensional k (X ⟶ Y)) ∧
    F.Linear k ∧ F.IsEquivalence ∧
      ∃ c : ∀ X Y : C, (X ⟶ Y) ≃ₗ[k] Module.Dual k (Y ⟶ F.obj X),
        (∀ ⦃X X' Y : C⦄ (f : X' ⟶ X) (g : X ⟶ Y)
            (h : Y ⟶ F.obj X'),
          c X' Y (f ≫ g) h = c X Y g (h ≫ F.map f)) ∧
          (∀ ⦃X Y Y' : C⦄ (g : X ⟶ Y) (f : Y ⟶ Y')
            (h : Y' ⟶ F.obj X),
            c X Y' (g ≫ f) h = c X Y g (f ≫ h))

/-- The Serre property with a scalar action supplied explicitly rather than inferred. -/
def IsSerreWith {k : Type w} [Field k] (linear : CategoryTheory.Linear k C) (F : C ⥤ C) : Prop :=
  @IsSerre C _ _ k _ linear F

/-- A fixed endofunctor has the Serre property exactly when it is the underlying functor of a
Serre functor and the category is Hom-finite. -/
theorem isSerre_iff {k : Type w} [Field k] [CategoryTheory.Linear k C] (F : C ⥤ C) :
    IsSerre k F ↔
      (∀ X Y : C, FiniteDimensional k (X ⟶ Y)) ∧
        ∃ S : SerreFunctor k C, S.toEquivalence.functor = F := sorry

end CategoryTheory.Functor

end
