/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.ToIsoClass
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassCopresheaf
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal
public import stacks_project.Chap90.Remarks_90_5_2_Grothendieck
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass

/-!
# Canonical morphism to fibrewise isomorphism classes

A category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` has a canonical
based morphism to the category of elements of its fibrewise isomorphism-class functor.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Canonical morphism to fibrewise isomorphism classes. -/
#check (CategoryTheory.BasedFunctor.toIsoClassFunctor :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type w} [Category.{v} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op],
    F ⥤ (Functor.fiberIsoClassFunctor p).Elements)

#check (CategoryTheory.BasedFunctor.toIsoClass :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type w} [Category.{v} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op],
    BasedCategory.ofFunctor p ⥤ᵇ
      BasedCategory.ofFunctor (CategoryOfElements.π (Functor.fiberIsoClassFunctor p)))

#check (CategoryTheory.BasedFunctor.toIsoClassFunctor_obj :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type w} [Category.{v} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op] (x : F),
    (CategoryTheory.BasedFunctor.toIsoClassFunctor p).obj x =
      ⟨p.obj x, Quotient.mk'' (Functor.Fiber.mk (rfl : p.obj x = p.obj x))⟩)

#check (CategoryTheory.BasedFunctor.toIsoClass_obj :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type w} [Category.{v} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op] (x : F),
    (CategoryTheory.BasedFunctor.toIsoClass p).obj x =
      ⟨p.obj x, Quotient.mk'' (Functor.Fiber.mk (rfl : p.obj x = p.obj x))⟩)

#check (CategoryTheory.BasedFunctor.toIsoClass_map :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type w} [Category.{v} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
    {x y : F} (φ : x ⟶ y),
    (CategoryOfElements.π (Functor.fiberIsoClassFunctor p)).map
        ((CategoryTheory.BasedFunctor.toIsoClass p).map φ) = p.map φ)

#check (CategoryTheory.BasedFunctor.toIsoClass_comp_π :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type w} [Category.{v} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op],
    (CategoryTheory.BasedFunctor.toIsoClass p).toFunctor ⋙
      CategoryOfElements.π (Functor.fiberIsoClassFunctor p) = p)
