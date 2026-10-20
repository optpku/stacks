/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Degree.Naturality
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of homological degrees of bounded-above left-derived models

The homological degree `n` is the cohomological degree `-n`.  This leaf exposes that common
indexing convention directly, so callers do not have to repeat integer coercions and negation.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.LeftDerived.homologicalDegree

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- Homological degree `n` is the model functor in cohomological degree `-n`. -/
@[stacks 015A "functor of bounded-above left-derived models in homological degree"]
noncomputable abbrev modelFunctor (n : ℕ) :
    (DerivedCategory.Minus A ⥤ DerivedCategory.Minus B) ⥤ A ⥤ B :=
  LeftDerived.degree.modelFunctor (-(n : ℤ))

/-- A transformation of bounded-above left-derived models acts on every homological degree. -/
@[stacks 015A "naturality of bounded-above left-derived homological degrees"]
noncomputable abbrev map
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (n : ℕ) :
    LeftDerived.homologicalDegree LF n ⟶
      LeftDerived.homologicalDegree LG n :=
  LeftDerived.degree.map τ (-(n : ℤ))

/-- The component of the induced homological-degree map is obtained by
applying homology to the corresponding model component. -/
@[simp]
theorem map_app
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (n : ℕ) (X : A) :
    (map τ n).app X =
      (DerivedCategory.Minus.homologyFunctor B (-(n : ℤ))).map
        (τ.app ((DerivedCategory.Minus.singleFunctor A 0).obj X)) := sorry

/-- The action on homological left-derived degrees preserves identity transformations. -/
@[simp, stacks 015A "identity on bounded-above left-derived homological degrees"]
theorem map_id
    (LF : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B) (n : ℕ) :
    map (𝟙 LF) n = 𝟙 (LeftDerived.homologicalDegree LF n) := sorry

/-- The action on homological left-derived degrees preserves composition. -/
@[simp, stacks 015A "composition on bounded-above left-derived homological degrees"]
theorem map_comp
    {LF LG LH : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (σ : LG ⟶ LH) (n : ℕ) :
    map (τ ≫ σ) n = map τ n ≫ map σ n := sorry

/-- An isomorphism of bounded-above left-derived models acts on every homological degree. -/
@[stacks 015A "isomorphisms of bounded-above left-derived homological degrees"]
noncomputable abbrev mapIso
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (e : LF ≅ LG) (n : ℕ) :
    LeftDerived.homologicalDegree LF n ≅
      LeftDerived.homologicalDegree LG n :=
  LeftDerived.degree.mapIso e (-(n : ℤ))

/-- The forward map of the homological-degree isomorphism is induced degreewise. -/
@[simp]
theorem mapIso_hom
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (e : LF ≅ LG) (n : ℕ) :
    (mapIso e n).hom = map e.hom n := sorry

/-- The inverse map of the homological-degree isomorphism is induced degreewise. -/
@[simp]
theorem mapIso_inv
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (e : LF ≅ LG) (n : ℕ) :
    (mapIso e n).inv = map e.inv n := sorry

/-- The forward component of a homological-degree model isomorphism. -/
@[simp]
theorem mapIso_hom_app
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (e : LF ≅ LG) (n : ℕ) (X : A) :
    (mapIso e n).hom.app X =
      (DerivedCategory.Minus.homologyFunctor B (-(n : ℤ))).map
        (e.hom.app ((DerivedCategory.Minus.singleFunctor A 0).obj X)) := sorry

/-- The inverse component of a homological-degree model isomorphism. -/
@[simp]
theorem mapIso_inv_app
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (e : LF ≅ LG) (n : ℕ) (X : A) :
    (mapIso e n).inv.app X =
      (DerivedCategory.Minus.homologyFunctor B (-(n : ℤ))).map
        (e.inv.app ((DerivedCategory.Minus.singleFunctor A 0).obj X)) := sorry

end CategoryTheory.Functor.LeftDerived.homologicalDegree
