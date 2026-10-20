/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Presheaf
public import ReasLib.CategoryTheory.Fibered.InheritedTopology
public import ReasLib.CategoryTheory.Fibered.Presheaf.Projective
public import ReasLib.CategoryTheory.Sites.CategoryHomology.Derived
public import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived fiber category homology

This leaf keeps the projective-resolution presentation of fiber category homology separate from
the bar-complex owner.  Import `CategoryHomology` for the hypothesis-light bar API; import this
leaf only when a derived-colimit presentation is part of the statement.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v wX vX w

namespace CategoryTheory.FiberedCategoryOver.FiberHomology.Derived

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (X : FiberedCategoryOver.{u, v, wX, vX} C)
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [HasWeakSheafify (X.p.inheritedTopology J) AddCommGrpCat.{w}]
variable [∀ V : C,
  HasProjectiveResolutions ((X.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{w})]
variable [∀ V : C,
  HasColimitsOfShape (X.p.Fiber V)ᵒᵖ AddCommGrpCat.{w}]
variable [Presheaf.PreservesProjectiveReindex X AddCommGrpCat.{w}]

/-- The derived-colimit category homology object of the restriction to one fiber. -/
@[stacks 08PI "derived fiber category homology object"]
abbrev homology
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (V : C)
    [HasProjectiveResolutions ((X.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{w})]
    [HasColimitsOfShape (X.p.Fiber V)ᵒᵖ AddCommGrpCat.{w}]
    (n : ℕ) :
    AddCommGrpCat.{w} :=
  CategoryHomology.categoryHomology
    (Presheaf.restrict X AddCommGrpCat.{w} F V) n

/-- The derived-colimit restriction map induced by a cartesian lift over a base arrow. -/
@[stacks 08PI "derived fiber category homology restriction map"]
abbrev restriction
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w})
    {U V : C} (f : V ⟶ U)
    [HasProjectiveResolutions ((X.p.Fiber U)ᵒᵖ ⥤ AddCommGrpCat.{w})]
    [HasProjectiveResolutions ((X.p.Fiber V)ᵒᵖ ⥤ AddCommGrpCat.{w})]
    [HasColimitsOfShape (X.p.Fiber U)ᵒᵖ AddCommGrpCat.{w}]
    [HasColimitsOfShape (X.p.Fiber V)ᵒᵖ AddCommGrpCat.{w}]
    [(Presheaf.reindex X AddCommGrpCat.{w} f).PreservesProjectiveObjects]
    (n : ℕ) :
    homology X F U n ⟶ homology X F V n :=
  CategoryHomology.map
    ((Functor.Cleavage.ofIsFibered X.p).reindex f)
    (Presheaf.cartesianRestriction X AddCommGrpCat.{w} F f) n

/-- Identity law for derived-colimit fiber homology restriction. -/
@[simp, stacks 08PI "derived fiber homology identity map"]
theorem restriction_id
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) (U : C) :
    restriction X F (𝟙 U) n = 𝟙 (homology X F U n) := sorry

/-- Composition law for derived-colimit fiber homology restriction. -/
@[simp, stacks 08PI "derived fiber homology composition map"]
theorem restriction_comp
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ)
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    restriction X F (g ≫ f) n =
      restriction X F f n ≫ restriction X F g n := sorry

/-- The presheaf whose value is derived-colimit fiber category homology. -/
@[stacks 08PI "derived fiber category homology presheaf"]
def presheaf
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    Cᵒᵖ ⥤ AddCommGrpCat.{w} where
  obj V := homology X F V.unop n
  map f := restriction X F f.unop n
  map_id := fun V => restriction_id X F n V.unop
  map_comp := fun f g => restriction_comp X F n f.unop g.unop

/-- The sheafification of the derived-colimit fiber homology presheaf. -/
@[stacks 08PI "derived fiber category homology sheaf"]
abbrev sheaf
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    Sheaf J AddCommGrpCat.{w} :=
  (presheafToSheaf J AddCommGrpCat.{w}).obj (presheaf X F n)

/-- The derived-colimit fiber homology map induced by a coefficient morphism. -/
@[stacks 08PI "derived fiber homology coefficient map component"]
noncomputable abbrev mapApp
    {F G : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) (U : C)
    [HasProjectiveResolutions ((X.p.Fiber U)ᵒᵖ ⥤ AddCommGrpCat.{w})]
    [HasColimitsOfShape (X.p.Fiber U)ᵒᵖ AddCommGrpCat.{w}]
    (n : ℕ) :
    homology X F U n ⟶ homology X G U n :=
  CategoryHomology.map (C := X.p.Fiber U) (C' := X.p.Fiber U)
    (𝟭 (X.p.Fiber U)) (Presheaf.restrictMap X AddCommGrpCat.{w} τ U) n

/-- Naturality of the derived-colimit coefficient map in the base category. -/
@[stacks 08PI "derived fiber homology coefficient map naturality"]
theorem map_naturality
    {F G : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) (n : ℕ)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (presheaf X F n).map f ≫ mapApp X τ V.unop n =
      mapApp X τ U.unop n ≫ (presheaf X G n).map f := sorry

/-- The presheaf map on derived-colimit fiber homology induced by a coefficient morphism. -/
@[stacks 08PI "derived fiber homology coefficient map"]
noncomputable abbrev map
    {F G : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) (n : ℕ) :
    presheaf X F n ⟶ presheaf X G n where
  app U := mapApp X τ U.unop n
  naturality := fun {_ _} f ↦ map_naturality X τ n f

/-- The component formula for a derived-colimit coefficient map. -/
@[simp, stacks 08PI "derived fiber homology coefficient map component formula"]
theorem map_app
    {F G : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) (n : ℕ) (U : Cᵒᵖ) :
    (map X τ n).app U = mapApp X τ U.unop n := sorry

/-- Derived-colimit fiber homology maps preserve identity coefficient morphisms. -/
@[simp, stacks 08PI "derived fiber homology coefficient identity"]
theorem map_id (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    map X (𝟙 F) n = 𝟙 (presheaf X F n) := sorry

/-- Derived-colimit fiber homology maps compose coefficient morphisms. -/
@[simp, stacks 08PI "derived fiber homology coefficient composition"]
theorem map_comp
    {F G H : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) (σ : G ⟶ H) (n : ℕ) :
    map X (τ ≫ σ) n = map X τ n ≫ map X σ n := sorry

/-- Derived fiber homology as a functor from total coefficient presheaves to base presheaves. -/
@[stacks 08PI "derived fiber homology coefficient functor"]
noncomputable def presheafFunctor (n : ℕ) :
    (X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{w}) where
  obj F := presheaf X F n
  map τ := map X τ n
  map_id F := map_id X F n
  map_comp τ σ := map_comp X τ σ n

/-- The derived fiber-homology coefficient functor is additive. -/
@[stacks 08PI "additivity of derived fiber homology coefficient functor"]
instance presheafFunctor.additive (n : ℕ) : (presheafFunctor X n).Additive := sorry

/-- Evaluation of the derived fiber-homology coefficient functor on objects. -/
@[simp, stacks 08PI "derived fiber homology coefficient functor object formula"]
theorem presheafFunctor_obj (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    (presheafFunctor X n).obj F = presheaf X F n := sorry

/-- Evaluation of the derived fiber-homology coefficient functor on morphisms. -/
@[simp, stacks 08PI "derived fiber homology coefficient functor map formula"]
theorem presheafFunctor_map
    {F G : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) (n : ℕ) :
    (presheafFunctor X n).map τ = map X τ n := sorry

/-- Derived fiber homology followed by sheafification, functorially in total coefficients. -/
@[stacks 08PI "derived fiber homology sheaf coefficient functor"]
noncomputable abbrev sheafFunctor (n : ℕ) :
    (X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ Sheaf J AddCommGrpCat.{w} :=
  presheafFunctor X n ⋙ presheafToSheaf J AddCommGrpCat.{w}

omit [HasWeakSheafify (X.p.inheritedTopology J) AddCommGrpCat.{w}] in
/-- Evaluation of the sheaf-valued derived fiber-homology functor on objects. -/
@[simp, stacks 08PI "derived fiber homology sheaf functor object formula"]
theorem sheafFunctor_obj (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    (sheafFunctor J X n).obj F = sheaf J X F n := sorry

/-- The sheaf-valued derived fiber-homology coefficient functor is additive. -/
@[stacks 08PI "additivity of derived fiber homology sheaf functor"]
instance sheafFunctor.additive (n : ℕ) : (sheafFunctor J X n).Additive := sorry

/-- The sheaf-level derived-colimit coefficient map. -/
@[stacks 08PI "derived fiber homology sheaf coefficient map"]
noncomputable abbrev sheafMap
    {F G : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) (n : ℕ) :
    sheaf J X F n ⟶ sheaf J X G n :=
  (sheafFunctor J X n).map τ

omit [HasWeakSheafify (X.p.inheritedTopology J) AddCommGrpCat.{w}] in
/-- Evaluation of the sheaf-valued derived fiber-homology functor on morphisms. -/
@[simp, stacks 08PI "derived fiber homology sheaf functor map formula"]
theorem sheafFunctor_map
    {F G : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}} (τ : F ⟶ G) (n : ℕ) :
    (sheafFunctor J X n).map τ = sheafMap J X τ n := sorry

/-- Derived fiber homology on sheaves of coefficients on the inherited total topology. -/
@[stacks 08PI "derived fiber homology functor on sheaves"]
noncomputable abbrev sheafOfSheafFunctor (n : ℕ) :
    Sheaf (X.p.inheritedTopology J) AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w} :=
  sheafToPresheaf (X.p.inheritedTopology J) AddCommGrpCat.{w} ⋙ sheafFunctor J X n

/-- The derived fiber-homology functor on sheaves is additive. -/
@[stacks 08PI "additivity of derived fiber homology sheaf-of-sheaves functor"]
instance sheafOfSheafFunctor.additive (n : ℕ) :
    (sheafOfSheafFunctor J X n).Additive := sorry

/-- The derived fiber-homology sheaf attached to a sheaf on the inherited total topology. -/
@[stacks 08PI "derived fiber homology sheaf of a sheaf"]
abbrev sheafOfSheaf
    (F : Sheaf (X.p.inheritedTopology J) AddCommGrpCat.{w}) (n : ℕ) :
    Sheaf J AddCommGrpCat.{w} :=
  (sheafOfSheafFunctor J X n).obj F

/-- The fiberwise derived-homology component induced by the sheafification unit on the total
presheaf. -/
@[stacks 08PI "derived fiber homology associated-sheaf component"]
abbrev associatedMapApp
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (V : Cᵒᵖ) (n : ℕ) :
    (presheaf X F n).obj V ⟶
      (presheaf X ((presheafToSheaf (X.p.inheritedTopology J)
        AddCommGrpCat.{w}).obj F).1 n).obj V :=
  mapApp X (toSheafify (X.p.inheritedTopology J) F) V.unop n

omit [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- Naturality of the derived-homology comparison induced by sheafification. -/
@[stacks 08PI "derived fiber homology associated-sheaf naturality"]
theorem associatedMap_naturality
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (presheaf X F n).map f ≫ associatedMapApp J X F V n =
      associatedMapApp J X F U n ≫
        (presheaf X ((presheafToSheaf (X.p.inheritedTopology J)
          AddCommGrpCat.{w}).obj F).1 n).map f := sorry

/-- The presheaf map on derived fiber homology induced by sheafification. -/
@[stacks 08PI "derived fiber homology associated-sheaf map"]
abbrev associatedMap
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    presheaf X F n ⟶
      presheaf X ((presheafToSheaf (X.p.inheritedTopology J)
        AddCommGrpCat.{w}).obj F).1 n :=
  map X (toSheafify (X.p.inheritedTopology J) F) n

/-- The sheaf-level derived-homology comparison induced by sheafification. -/
@[stacks 08PI "derived fiber homology associated-sheaf morphism"]
abbrev sheafAssociatedHom
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    sheaf J X F n ⟶
      sheafOfSheaf J X
        ((presheafToSheaf (X.p.inheritedTopology J) AddCommGrpCat.{w}).obj F) n :=
  sheafMap J X (toSheafify (X.p.inheritedTopology J) F) n

/-- Sheafification does not change the sheafified derived fiber-homology presheaf. -/
@[stacks 08PI "derived fiber homology sheafification invariance"]
theorem sheafAssociatedHom_isIso
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    IsIso (sheafAssociatedHom J X F n) := sorry

/-- Canonical invertibility instance for the derived fiber-homology sheafification comparison. -/
instance sheafAssociatedHom.instIsIso
    (F : X.totalᵒᵖ ⥤ AddCommGrpCat.{w}) (n : ℕ) :
    IsIso (sheafAssociatedHom J X F n) :=
  sorry

end CategoryTheory.FiberedCategoryOver.FiberHomology.Derived
