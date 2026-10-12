/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Comparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of degrees of bounded-below right-derived models

A transformation between arbitrary bounded-below right-derived models induces a transformation
between every degree functor.  Keeping this construction below the canonical-model layer lets
comparison and uniqueness arguments reuse it without first choosing the project's standard model.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.degree

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- Evaluation in degree `i` is functorial in the chosen bounded-below
right-derived model. -/
@[stacks 015A "functor of bounded-below right-derived models in one degree"]
noncomputable def modelFunctor (i : ℤ) :
    (DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) ⥤ A ⥤ B :=
  ((Functor.whiskeringLeft A (DerivedCategory.Plus A)
      (DerivedCategory.Plus B)).obj
      (DerivedCategory.Plus.singleFunctor A 0)) ⋙
    ((Functor.whiskeringRight A (DerivedCategory.Plus B) B).obj
      (DerivedCategory.Plus.homologyFunctor B i))

/-- A transformation of bounded-below right-derived models acts on every degree functor. -/
@[stacks 015A "naturality of bounded-below right-derived degrees"]
noncomputable def map
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (τ : RF ⟶ RG) (i : ℤ) :
    RightDerived.degree RF i ⟶ RightDerived.degree RG i :=
  (modelFunctor i).map τ

/-- The component of the induced degree map is obtained by applying homology
to the corresponding component of the model transformation. -/
@[simp, stacks 015A "component of a bounded-below right-derived degree map"]
theorem map_app
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (τ : RF ⟶ RG) (i : ℤ) (X : A) :
    (map τ i).app X =
      (DerivedCategory.Plus.homologyFunctor B i).map
        (τ.app ((DerivedCategory.Plus.singleFunctor A 0).obj X)) := sorry

/-- The action on right-derived degrees preserves identity transformations. -/
@[simp, stacks 015A "identity on bounded-below right-derived degrees"]
theorem map_id
    (RF : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) (i : ℤ) :
    map (𝟙 RF) i = 𝟙 (RightDerived.degree RF i) := sorry

/-- The action on right-derived degrees preserves composition of transformations. -/
@[simp, stacks 015A "composition on bounded-below right-derived degrees"]
theorem map_comp
    {RF RG RH : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (τ : RF ⟶ RG) (σ : RG ⟶ RH) (i : ℤ) :
    map (τ ≫ σ) i = map τ i ≫ map σ i := sorry

/-- An isomorphism of bounded-below right-derived models acts on every degree functor. -/
@[stacks 015A "isomorphisms of bounded-below right-derived degrees"]
noncomputable def mapIso
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (e : RF ≅ RG) (i : ℤ) :
    RightDerived.degree RF i ≅ RightDerived.degree RG i :=
  (modelFunctor i).mapIso e

/-- The forward map of `mapIso` is the induced map on right-derived degrees. -/
@[simp]
theorem mapIso_hom
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (e : RF ≅ RG) (i : ℤ) :
    (mapIso e i).hom = map e.hom i := sorry

/-- The inverse map of `mapIso` is the induced map on right-derived degrees. -/
@[simp]
theorem mapIso_inv
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (e : RF ≅ RG) (i : ℤ) :
    (mapIso e i).inv = map e.inv i := sorry

/-- The forward component of a model isomorphism in degree `i`. -/
@[simp]
theorem mapIso_hom_app
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (e : RF ≅ RG) (i : ℤ) (X : A) :
    (mapIso e i).hom.app X =
      (DerivedCategory.Plus.homologyFunctor B i).map
        (e.hom.app ((DerivedCategory.Plus.singleFunctor A 0).obj X)) := sorry

/-- The inverse component of a model isomorphism in degree `i`. -/
@[simp]
theorem mapIso_inv_app
    {RF RG : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B}
    (e : RF ≅ RG) (i : ℤ) (X : A) :
    (mapIso e i).inv.app X =
      (DerivedCategory.Plus.homologyFunctor B i).map
        (e.inv.app ((DerivedCategory.Plus.singleFunctor A 0).obj X)) := sorry

end CategoryTheory.Functor.RightDerived.degree
