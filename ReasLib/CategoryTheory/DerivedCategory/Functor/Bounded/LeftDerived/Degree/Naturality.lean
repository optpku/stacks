module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Comparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of degrees of bounded-above left-derived models

A transformation between arbitrary bounded-above left-derived models induces a transformation
between every cohomological degree functor.  This model-independent layer is suitable for
comparison and uniqueness arguments as well as canonical derived functors.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.LeftDerived.degree

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- Evaluation in degree `i` is functorial in the chosen bounded-above
left-derived model. -/
@[stacks 015A "functor of bounded-above left-derived models in one degree"]
noncomputable def modelFunctor (i : ℤ) :
    (DerivedCategory.Minus A ⥤ DerivedCategory.Minus B) ⥤ A ⥤ B :=
  ((Functor.whiskeringLeft A (DerivedCategory.Minus A)
      (DerivedCategory.Minus B)).obj
      (DerivedCategory.Minus.singleFunctor A 0)) ⋙
    ((Functor.whiskeringRight A (DerivedCategory.Minus B) B).obj
      (DerivedCategory.Minus.homologyFunctor B i))

/-- A transformation of bounded-above left-derived models acts on every degree functor. -/
@[stacks 015A "naturality of bounded-above left-derived degrees"]
noncomputable def map
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (i : ℤ) :
    LeftDerived.degree LF i ⟶ LeftDerived.degree LG i :=
  (modelFunctor i).map τ

/-- The component of the induced degree map is obtained by applying homology
to the corresponding component of the model transformation. -/
@[simp, stacks 015A "component of a bounded-above left-derived degree map"]
theorem map_app
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (i : ℤ) (X : A) :
    (map τ i).app X =
      (DerivedCategory.Minus.homologyFunctor B i).map
        (τ.app ((DerivedCategory.Minus.singleFunctor A 0).obj X)) := sorry

/-- The action on left-derived degrees preserves identity transformations. -/
@[simp, stacks 015A "identity on bounded-above left-derived degrees"]
theorem map_id
    (LF : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B) (i : ℤ) :
    map (𝟙 LF) i = 𝟙 (LeftDerived.degree LF i) := sorry

/-- The action on left-derived degrees preserves composition of transformations. -/
@[simp, stacks 015A "composition on bounded-above left-derived degrees"]
theorem map_comp
    {LF LG LH : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (τ : LF ⟶ LG) (σ : LG ⟶ LH) (i : ℤ) :
    map (τ ≫ σ) i = map τ i ≫ map σ i := sorry

/-- An isomorphism of bounded-above left-derived models acts on every degree functor. -/
@[stacks 015A "isomorphisms of bounded-above left-derived degrees"]
noncomputable def mapIso
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (e : LF ≅ LG) (i : ℤ) :
    LeftDerived.degree LF i ≅ LeftDerived.degree LG i :=
  (modelFunctor i).mapIso e

/-- The forward map of `mapIso` is the induced map on left-derived degrees. -/
@[simp]
theorem mapIso_hom
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (e : LF ≅ LG) (i : ℤ) :
    (mapIso e i).hom = map e.hom i := sorry

/-- The inverse map of `mapIso` is the induced map on left-derived degrees. -/
@[simp]
theorem mapIso_inv
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (e : LF ≅ LG) (i : ℤ) :
    (mapIso e i).inv = map e.inv i := sorry

/-- The forward component of a model isomorphism in degree `i`. -/
@[simp]
theorem mapIso_hom_app
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (e : LF ≅ LG) (i : ℤ) (X : A) :
    (mapIso e i).hom.app X =
      (DerivedCategory.Minus.homologyFunctor B i).map
        (e.hom.app ((DerivedCategory.Minus.singleFunctor A 0).obj X)) := sorry

/-- The inverse component of a model isomorphism in degree `i`. -/
@[simp]
theorem mapIso_inv_app
    {LF LG : DerivedCategory.Minus A ⥤ DerivedCategory.Minus B}
    (e : LF ≅ LG) (i : ℤ) (X : A) :
    (mapIso e i).inv.app X =
      (DerivedCategory.Minus.homologyFunctor B i).map
        (e.inv.app ((DerivedCategory.Minus.singleFunctor A 0).obj X)) := sorry

end CategoryTheory.Functor.LeftDerived.degree
