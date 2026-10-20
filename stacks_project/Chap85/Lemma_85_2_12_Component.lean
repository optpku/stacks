/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Spaces
public import ReasLib.CategoryTheory.Sites.Product

/-!
# Degree components of sheaves on a constant simplicial Zariski site

For a topological space `X`, sheaves on the product site
`SimplexCategoryᵒᵖ × Opens X` with coverings in the second factor restrict
along `Prod.sectR n` to ordinary Zariski sheaves `F_n`, assembled into a
cosimplicial sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite TopologicalSpace
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.ConstantSimplicialSpace

variable {X : Type u} [TopologicalSpace X]
variable {A : Type w} [Category.{v} A]

/-- Degree-`n` inclusion of `Opens X` into the constant simplicial Zariski site is
continuous. -/
instance sectR_isContinuous (n : SimplexCategoryᵒᵖ) :
    (Prod.sectR n (Opens X)).IsContinuous
      (Opens.grothendieckTopology X)
      ((Opens.grothendieckTopology X).onSnd SimplexCategoryᵒᵖ) :=
  sorry

/-- Degree-`n` inclusion of `Opens X` into the constant simplicial Zariski site is
cocontinuous. -/
instance sectR_isCocontinuous (n : SimplexCategoryᵒᵖ) :
    (Prod.sectR n (Opens X)).IsCocontinuous
      (Opens.grothendieckTopology X)
      ((Opens.grothendieckTopology X).onSnd SimplexCategoryᵒᵖ) :=
  sorry

/-- The degree-`n` component of a sheaf on the constant simplicial Zariski site,
obtained by continuous pushforward along `Prod.sectR n`. -/
def component (n : SimplexCategoryᵒᵖ) :
    Sheaf ((Opens.grothendieckTopology X).onSnd SimplexCategoryᵒᵖ) A ⥤
      Sheaf (Opens.grothendieckTopology X) A :=
  (Prod.sectR n (Opens X)).sheafPushforwardContinuous A
    (Opens.grothendieckTopology X)
    ((Opens.grothendieckTopology X).onSnd SimplexCategoryᵒᵖ)

/-- Sections of the degree-`n` component over `U` are the sections of `F` at `(n, U)`. -/
theorem component_obj (n : SimplexCategoryᵒᵖ)
    (F : Sheaf ((Opens.grothendieckTopology X).onSnd SimplexCategoryᵒᵖ) A)
    (U : Opens X) :
    ((component n).obj F).obj.obj (op U) = F.obj.obj (op (n, U)) :=
  sorry

/-- The degree-`n` component is functorial in the sheaf. -/
theorem component_map (n : SimplexCategoryᵒᵖ)
    {F G : Sheaf ((Opens.grothendieckTopology X).onSnd SimplexCategoryᵒᵖ) A}
    (α : F ⟶ G) (U : Opens X) :
    ((component n).map α).hom.app (op U) = α.hom.app (op (n, U)) :=
  sorry

/-- The natural transformation `Prod.sectR n ⟶ Prod.sectR m` induced by a map of
simplicial degrees. -/
def sectRMap {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    Prod.sectR n (Opens X) ⟶ Prod.sectR m (Opens X) where
  app U := Prod.mkHom f (𝟙 U)
  naturality := fun _ _ _ ↦ sorry

/-- Identity maps of simplicial degrees induce identity natural transformations of
`Prod.sectR`. -/
theorem sectRMap_id (n : SimplexCategoryᵒᵖ) :
    sectRMap (𝟙 n) = 𝟙 (Prod.sectR n (Opens X)) :=
  sorry

/-- Composition of simplicial-degree maps induces composition of `Prod.sectR`
natural transformations. -/
theorem sectRMap_comp {n m p : SimplexCategoryᵒᵖ} (f : n ⟶ m) (g : m ⟶ p) :
    sectRMap (f ≫ g) =
      (sectRMap f ≫ sectRMap g : Prod.sectR n (Opens X) ⟶ Prod.sectR p (Opens X)) :=
  sorry

/-- The underlying functor of `toCosimplicial` on a single sheaf. -/
def toCosimplicialObj
    (F : Sheaf ((Opens.grothendieckTopology X).onSnd SimplexCategoryᵒᵖ) A) :
    SimplexCategory ⥤ Sheaf (Opens.grothendieckTopology X) A where
  obj n := (component (op n)).obj F
  map f :=
    (sheafPushforwardContinuousNatTrans (sectRMap f.op) A
        (Opens.grothendieckTopology X)
        ((Opens.grothendieckTopology X).onSnd SimplexCategoryᵒᵖ)).app F
  map_id := sorry
  map_comp := sorry

/-- A sheaf on the constant simplicial Zariski site determines a cosimplicial
sheaf on `X` by restriction to each degree. -/
def toCosimplicial :
    Sheaf ((Opens.grothendieckTopology X).onSnd SimplexCategoryᵒᵖ) A ⥤
      CosimplicialObject (Sheaf (Opens.grothendieckTopology X) A) where
  obj F := toCosimplicialObj F
  map {F G} α :=
    { app := fun n ↦ (component (op n)).map α
      naturality := fun _ _ _ ↦ sorry }
  map_id := sorry
  map_comp := sorry

/-- On objects, `toCosimplicial` evaluates as the degree-`n` component. -/
theorem toCosimplicial_obj
    (F : Sheaf ((Opens.grothendieckTopology X).onSnd SimplexCategoryᵒᵖ) A)
    (n : SimplexCategory) :
    (toCosimplicial.obj F).obj n = (component (op n)).obj F :=
  sorry

/-- Coface maps of `toCosimplicial.obj F` are the degree maps associated to
`SimplexCategory.δ`. -/
theorem toCosimplicial_δ
    (F : Sheaf ((Opens.grothendieckTopology X).onSnd SimplexCategoryᵒᵖ) A)
    {n : ℕ} (i : Fin (n + 2)) :
    (toCosimplicial.obj F).δ i =
      (toCosimplicial.obj F).map (SimplexCategory.δ i) :=
  sorry

end CategoryTheory.ConstantSimplicialSpace
