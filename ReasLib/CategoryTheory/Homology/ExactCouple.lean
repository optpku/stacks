/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact Couples

This module owns the elementary exact-couple datum and its page-one
differential complex.  It is independent of a particular construction of the
derived couple or associated spectral sequence.
-/

@[expose] public section

namespace CategoryTheory

universe v u

section

/-- 011Q (Definition 12.21.1): an exact couple consists of two objects `A` and `E`,
endomorphism `α : A ⟶ A`, and maps `f : E ⟶ A` and `g : A ⟶ E`, whose three
cyclic short complexes are exact. -/
@[stacks 011Q]
structure ExactCouple (C : Type u) [Category.{v} C] [Limits.HasZeroMorphisms C] where
  /-- The outer object of the exact couple. -/
  A : C
  /-- The page object of the exact couple. -/
  E : C
  /-- The endomorphism on the outer object. -/
  α : A ⟶ A
  /-- The map from the page object to the outer object. -/
  f : E ⟶ A
  /-- The map from the outer object to the page object. -/
  g : A ⟶ E
  /-- The composite `f ≫ α` vanishes. -/
  f_comp_α : f ≫ α = 0
  /-- The composite `g ≫ f` vanishes. -/
  g_comp_f : g ≫ f = 0
  /-- The composite `α ≫ g` vanishes. -/
  α_comp_g : α ≫ g = 0
  /-- Exactness of `E ⟶ A ⟶ A`. -/
  exact_f_α : (ShortComplex.mk f α f_comp_α).Exact
  /-- Exactness of `A ⟶ E ⟶ A`. -/
  exact_g_f : (ShortComplex.mk g f g_comp_f).Exact
  /-- Exactness of `A ⟶ A ⟶ E`. -/
  exact_α_g : (ShortComplex.mk α g α_comp_g).Exact

namespace ExactCouple

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]

variable (X : ExactCouple C)

/-- The page differential of an exact couple. -/
@[stacks 011Q "exact-couple page differential"]
abbrev d : X.E ⟶ X.E :=
  X.f ≫ X.g

/-- Computation rule for the page differential. -/
@[simp]
theorem d_eq_f_comp_g : X.d = X.f ≫ X.g := rfl

/-- The page differential squares to zero. -/
@[simp, stacks 011Q "exact-couple page differential square"]
theorem d_comp_d : X.d ≫ X.d = 0 := by
  calc
    X.d ≫ X.d = X.f ≫ (X.g ≫ X.f) ≫ X.g := by simp only [d, Category.assoc]
    _ = 0 := by rw [X.g_comp_f, Limits.zero_comp, Limits.comp_zero]

/-- The explicit page short complex associated to a supplied square-zero witness for the
exact-couple differential.  This proof-parametric owner lets constructions retain their own
square-zero certificate instead of depending on a global theorem placeholder. -/
@[stacks 011Q "page short complex with square-zero witness"]
def pageShortComplexOf (X : ExactCouple C) (d_squared : X.d ≫ X.d = 0) :
    ShortComplex C :=
  ShortComplex.mk X.d X.d d_squared

/-- The one-object page complex associated to a supplied square-zero witness for the
exact-couple differential. -/
@[stacks 011Q "page complex with square-zero witness"]
noncomputable def pageOf (X : ExactCouple C) (d_squared : X.d ≫ X.d = 0) :
    HomologicalComplex C (ComplexShape.refl PUnit.{1}) where
  X := fun _ ↦ X.E
  d := fun _ _ ↦ X.d
  shape := fun i j h ↦ (h (Subsingleton.elim i j)).elim
  d_comp_d' := fun _ _ _ _ _ ↦ d_squared

/-- The map `g` is a cycle for the page differential. -/
@[simp]
theorem g_comp_d : X.g ≫ X.d = 0 := by
  simp [d, ← Category.assoc, X.g_comp_f]

/-- The page differential is annihilated by `f`. -/
@[simp]
theorem d_comp_f : X.d ≫ X.f = 0 := by
  simp [d, Category.assoc, X.g_comp_f]

/-- A morphism of exact couples consists of maps on the `A`- and `E`-objects
that commute with the three structure morphisms. -/
@[ext, stacks 011Q "exact-couple morphism"]
structure Hom (X Y : ExactCouple C) where
  /-- The component on the `A`-objects. -/
  a : X.A ⟶ Y.A
  /-- The component on the `E`-objects. -/
  e : X.E ⟶ Y.E
  /-- Compatibility with the endomorphisms `α`. -/
  comm_α : X.α ≫ a = a ≫ Y.α
  /-- Compatibility with the maps `f`. -/
  comm_f : X.f ≫ a = e ≫ Y.f
  /-- Compatibility with the maps `g`. -/
  comm_g : X.g ≫ e = a ≫ Y.g

namespace Hom

/-- The identity morphism of an exact couple. -/
def id (X : ExactCouple C) : Hom X X where
  a := 𝟙 X.A
  e := 𝟙 X.E
  comm_α := by simp
  comm_f := by simp
  comm_g := by simp

/-- Composition of morphisms of exact couples. -/
def comp {X Y Z : ExactCouple C} (φ : Hom X Y) (ψ : Hom Y Z) : Hom X Z where
  a := φ.a ≫ ψ.a
  e := φ.e ≫ ψ.e
  comm_α := by
    rw [← Category.assoc, φ.comm_α, Category.assoc, ψ.comm_α, ← Category.assoc]
  comm_f := by
    rw [← Category.assoc, φ.comm_f, Category.assoc, ψ.comm_f, ← Category.assoc]
  comm_g := by
    rw [← Category.assoc, φ.comm_g, Category.assoc, ψ.comm_g, ← Category.assoc]

end Hom

/-- Exact couples form a category under componentwise composition. -/
instance : Category (ExactCouple C) where
  Hom X Y := Hom X Y
  id := Hom.id
  comp φ ψ := Hom.comp φ ψ
  id_comp := by
    intro X Y φ
    apply Hom.ext <;> simp [Hom.comp, Hom.id]
  comp_id := by
    intro X Y φ
    apply Hom.ext <;> simp [Hom.comp, Hom.id]
  assoc := by
    intro W X Y Z φ ψ χ
    apply Hom.ext <;> simp [Hom.comp, Category.assoc]

/-- Computation rule for the `A`-component of an identity exact-couple morphism. -/
@[simp]
theorem id_a (X : ExactCouple C) : (𝟙 X : X ⟶ X).a = 𝟙 X.A := rfl

/-- Computation rule for the `E`-component of an identity exact-couple morphism. -/
@[simp]
theorem id_e (X : ExactCouple C) : (𝟙 X : X ⟶ X).e = 𝟙 X.E := rfl

/-- Computation rule for the `A`-component of a composite exact-couple morphism. -/
@[simp]
theorem comp_a {X Y Z : ExactCouple C} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ ≫ ψ).a = φ.a ≫ ψ.a := rfl

/-- Computation rule for the `E`-component of a composite exact-couple morphism. -/
@[simp]
theorem comp_e {X Y Z : ExactCouple C} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ ≫ ψ).e = φ.e ≫ ψ.e := rfl

/-- The `E`-component of an exact-couple morphism commutes with page differentials. -/
@[reassoc]
theorem Hom.e_comp_d {X Y : ExactCouple C} (φ : Hom X Y) :
    φ.e ≫ Y.d = X.d ≫ φ.e := by
  dsimp only [d]
  rw [← Category.assoc, ← φ.comm_f, Category.assoc, ← φ.comm_g, ← Category.assoc]

/-- The unique object of `pageOf` is the page object of the exact couple. -/
@[simp]
theorem pageOf_X (X : ExactCouple C) (d_squared : X.d ≫ X.d = 0) :
    (X.pageOf d_squared).X PUnit.unit = X.E := rfl

/-- The unique differential of `pageOf` is the exact-couple page differential. -/
@[simp]
theorem pageOf_d (X : ExactCouple C) (d_squared : X.d ≫ X.d = 0) :
    (X.pageOf d_squared).d PUnit.unit PUnit.unit = X.d := rfl

/-- Extracting the unique short complex of `pageOf` recovers `pageShortComplexOf` with the
same square-zero witness. -/
@[simp]
theorem pageOf_sc (X : ExactCouple C) (d_squared : X.d ≫ X.d = 0) :
    (X.pageOf d_squared).sc PUnit.unit = X.pageShortComplexOf d_squared := rfl

/-- A morphism of exact couples induces a map of page complexes when the square-zero witnesses
used to construct their concrete data are supplied explicitly. -/
@[stacks 011Q "page map with square-zero witnesses"]
def Hom.pageMapOf {X Y : ExactCouple C} (φ : Hom X Y)
    (d_squared_X : X.d ≫ X.d = 0) (d_squared_Y : Y.d ≫ Y.d = 0) :
    X.pageOf d_squared_X ⟶ Y.pageOf d_squared_Y where
  f _ := φ.e
  comm' := by
    intro i j hij
    exact φ.e_comp_d

/-- The unique component of `pageMapOf` is the page component of the exact-couple morphism. -/
@[simp]
theorem Hom.pageMapOf_f {X Y : ExactCouple C} (φ : Hom X Y)
    (d_squared_X : X.d ≫ X.d = 0) (d_squared_Y : Y.d ≫ Y.d = 0) :
    (φ.pageMapOf d_squared_X d_squared_Y).f PUnit.unit = φ.e := rfl

/-- The canonical one-object homological complex carried by the page differential of an exact
couple.  The square-zero certificate is intrinsic to the exact-couple datum; use `pageOf` when a
construction must retain a particular certificate. -/
@[stacks 011Q "page differential complex"]
noncomputable def page (X : ExactCouple C) : HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
  X.pageOf X.d_comp_d

/-- The unique object of the canonical page complex is the page object of the exact couple. -/
@[simp]
theorem page_X (X : ExactCouple C) : X.page.X PUnit.unit = X.E := rfl

/-- The unique differential of the canonical page complex is the exact-couple differential. -/
@[simp]
theorem page_d (X : ExactCouple C) : X.page.d PUnit.unit PUnit.unit = X.d := rfl

/-- The explicit short complex `E ⟶ E ⟶ E` associated to the canonical page differential. -/
@[stacks 011Q "page differential short complex"]
def pageShortComplex (X : ExactCouple C) : ShortComplex C :=
  X.pageShortComplexOf X.d_comp_d

/-- The short complex extracted from the canonical page complex is `pageShortComplex`. -/
@[simp]
theorem page_sc (X : ExactCouple C) : X.page.sc PUnit.unit = X.pageShortComplex := rfl

/-- The first map of the canonical page short complex is the page differential. -/
@[simp]
theorem pageShortComplex_f (X : ExactCouple C) : X.pageShortComplex.f = X.d := rfl

/-- The second map of the canonical page short complex is the page differential. -/
@[simp]
theorem pageShortComplex_g (X : ExactCouple C) : X.pageShortComplex.g = X.d := rfl

/-- A morphism of exact couples induces a chain map between their canonical page complexes. -/
@[stacks 011Q "canonical page map"]
def Hom.pageMap {X Y : ExactCouple C} (φ : Hom X Y) : X.page ⟶ Y.page :=
  φ.pageMapOf X.d_comp_d Y.d_comp_d

/-- The unique component of the canonical page map is the page component of the exact-couple
morphism. -/
@[simp]
theorem Hom.pageMap_f {X Y : ExactCouple C} (φ : Hom X Y) :
    φ.pageMap.f PUnit.unit = φ.e := rfl

namespace PageMap

/-- Canonical page maps preserve identity morphisms of exact couples. -/
@[simp]
theorem id (X : ExactCouple C) :
    (𝟙 X : X ⟶ X).pageMap = 𝟙 X.page := by
  apply HomologicalComplex.hom_ext
  intro i
  rfl

/-- Canonical page maps preserve composition of exact-couple morphisms. -/
@[simp]
theorem comp {X Y Z : ExactCouple C} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (φ ≫ ψ).pageMap = φ.pageMap ≫ ψ.pageMap := by
  apply HomologicalComplex.hom_ext
  intro i
  rfl

end PageMap

/-- The canonical functor sending an exact couple to its page differential complex. -/
@[stacks 011Q "page differential functor"]
noncomputable def pageFunctor (C : Type u) [Category.{v} C] [Limits.HasZeroMorphisms C] :
    ExactCouple C ⥤ HomologicalComplex C (ComplexShape.refl PUnit.{1}) where
  obj X := X.page
  map φ := φ.pageMap
  map_id := PageMap.id
  map_comp := PageMap.comp

namespace PageFunctor

/-- The page functor evaluates an object at its canonical page complex. -/
@[simp]
theorem obj (X : ExactCouple C) :
    (pageFunctor C).obj X = X.page := rfl

/-- The page functor sends a morphism to its canonical page map. -/
@[simp]
theorem map {X Y : ExactCouple C} (φ : X ⟶ Y) :
    (pageFunctor C).map φ = φ.pageMap := rfl

end PageFunctor

end ExactCouple

end

end CategoryTheory
