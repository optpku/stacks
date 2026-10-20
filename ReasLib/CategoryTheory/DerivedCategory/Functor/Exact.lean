/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Exactness.Composition
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of exact functors on derived categories

This leaf promotes passage to derived categories from an objectwise
construction to a functor on the category of bundled exact functors.  Its
action on natural transformations is the canonical localization lift.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u₁ u₂ v₁ v₂ w₁ w₂

namespace CategoryTheory.ExactFunctor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

/-- The functor on derived categories associated to a bundled exact functor. -/
noncomputable abbrev mapDerivedCategory (F : A ⥤ₑ B) :
    DerivedCategory A ⥤ DerivedCategory B :=
  CategoryTheory.Functor.mapDerivedCategory F.obj

end CategoryTheory.ExactFunctor

namespace CategoryTheory.ExactFunctor.MapDerivedCategory

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

/-- The natural transformation on derived categories induced by a morphism of
bundled exact functors.  It is the canonical localization lift of the map on
cochain complexes. -/
@[stacks 015F "exact functors act on derived-category maps"]
noncomputable def map {F G : A ⥤ₑ B} (α : F ⟶ G) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory :=
  Localization.liftNatTrans
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
    (HomologicalComplex.quasiIso A (up ℤ))
    (F.obj.mapHomologicalComplex (up ℤ) ⋙
      (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B))
    (G.obj.mapHomologicalComplex (up ℤ) ⋙
      (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B))
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex α.hom (up ℤ))
      (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B))

/-- Computation of the derived natural transformation on an object in the
image of the localization functor. -/
@[stacks 015F "compute the derived action on localization objects"]
theorem map_app_Q {F G : A ⥤ₑ B} (α : F ⟶ G) (K : CochainComplex A ℤ) :
    (map α).app (DerivedCategory.Q.obj K) =
      F.obj.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex α.hom (up ℤ)).app K) ≫
        G.obj.mapDerivedCategoryFactors.inv.app K := sorry

/-- The derived action sends identity transformations to identity
transformations. -/
@[simp]
theorem map_id (F : A ⥤ₑ B) :
    map (𝟙 F) = 𝟙 F.mapDerivedCategory := sorry

/-- The derived action preserves vertical composition of natural
transformations. -/
@[simp]
theorem map_comp {F G H : A ⥤ₑ B} (α : F ⟶ G) (β : G ⟶ H) :
    map (α ≫ β) = map α ≫ map β := sorry

variable (A B) in
/-- Passage from bundled exact functors to their functors on derived
categories, including the action on natural transformations. -/
@[stacks 015F "exact functors act functorially on derived categories"]
noncomputable def functor :
    (A ⥤ₑ B) ⥤ (DerivedCategory A ⥤ DerivedCategory B) where
  obj F := F.mapDerivedCategory
  map α := map α
  map_id F := map_id F
  map_comp α β := map_comp α β

/-- Object computation for the functorial derived action. -/
@[simp]
theorem functor_obj (F : A ⥤ₑ B) :
    (functor A B).obj F = F.mapDerivedCategory := sorry

/-- Morphism computation for the functorial derived action. -/
@[simp]
theorem functor_map {F G : A ⥤ₑ B} (α : F ⟶ G) :
    (functor A B).map α = map α := sorry

/-- A natural isomorphism of bundled exact functors induces a natural
isomorphism of their functors on derived categories. -/
noncomputable abbrev mapIso {F G : A ⥤ₑ B} (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  (functor A B).mapIso e

namespace mapIso

/-- The forward component of the derived image of an exact-functor
isomorphism is the derived image of its forward morphism. -/
@[simp]
theorem hom_app {F G : A ⥤ₑ B} (e : F ≅ G) (K : DerivedCategory A) :
    (mapIso e).hom.app K = (map e.hom).app K := sorry

/-- The inverse component of the derived image of an exact-functor
isomorphism is the derived image of its inverse morphism. -/
@[simp]
theorem inv_app {F G : A ⥤ₑ B} (e : F ≅ G) (K : DerivedCategory A) :
    (mapIso e).inv.app K = (map e.inv).app K := sorry

end mapIso

end CategoryTheory.ExactFunctor.MapDerivedCategory

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

/-- A natural isomorphism of exact functors induces a natural isomorphism of
their functors on derived categories. -/
@[stacks 015F "natural isomorphisms of exact derived functors"]
noncomputable def MapDerivedCategory.functorIso
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) : F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  let e' : ExactFunctor.of F ≅ ExactFunctor.of G :=
    ObjectProperty.isoMk (exactFunctor A B) e
  ExactFunctor.MapDerivedCategory.mapIso e'

/-- A natural isomorphism of exact functors induces an isomorphism between
their values on an arbitrary object of the derived category. -/
@[stacks 015F "objectwise isomorphism of exact derived functors"]
noncomputable abbrev MapDerivedCategory.objIso
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (K : DerivedCategory A) :
    F.mapDerivedCategory.obj K ≅ G.mapDerivedCategory.obj K :=
  (MapDerivedCategory.functorIso e).app K

/-- Forward naturality of the objectwise comparison induced by a natural
isomorphism of exact functors. -/
@[reassoc]
theorem MapDerivedCategory.objIso_hom_naturality
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) {K L : DerivedCategory A} (f : K ⟶ L) :
    F.mapDerivedCategory.map f ≫ (MapDerivedCategory.objIso e L).hom =
      (MapDerivedCategory.objIso e K).hom ≫ G.mapDerivedCategory.map f := sorry

/-- Inverse naturality of the objectwise comparison induced by a natural
isomorphism of exact functors. -/
@[reassoc]
theorem MapDerivedCategory.objIso_inv_naturality
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) {K L : DerivedCategory A} (f : K ⟶ L) :
    G.mapDerivedCategory.map f ≫ (MapDerivedCategory.objIso e L).inv =
      (MapDerivedCategory.objIso e K).inv ≫ F.mapDerivedCategory.map f := sorry

namespace MapDerivedCategory.functorIso

/-- The components of `MapDerivedCategory.functorIso` are the primitive
objectwise comparisons. -/
@[simp]
theorem app
    {F G : A ⥤ B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (K : DerivedCategory A) :
    (MapDerivedCategory.functorIso e).app K =
      MapDerivedCategory.objIso e K := sorry

end MapDerivedCategory.functorIso

end CategoryTheory.Functor
