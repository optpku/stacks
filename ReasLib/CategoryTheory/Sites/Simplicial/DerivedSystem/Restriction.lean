/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.Cartesian
public import ReasLib.CategoryTheory.Sites.Simplicial.DerivedSystem
public import ReasLib.CategoryTheory.Sites.Topos.Composition

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram.{u, v, w} C J]
variable [UnivLE.{max u v, w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

namespace AbelianDerived

/-- The family of abelian inverse-image functors is additive. -/
instance inverseImage_additive :
    ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ((abelianInverseImageExact C J φ).obj).Additive := sorry

/-- The family of abelian inverse-image functors preserves finite limits. -/
instance inverseImage_preservesFiniteLimits :
    ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      PreservesFiniteLimits (abelianInverseImageExact C J φ).obj := sorry

/-- The family of abelian inverse-image functors preserves finite colimits. -/
instance inverseImage_preservesFiniteColimits :
    ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      PreservesFiniteColimits (abelianInverseImageExact C J φ).obj := sorry

/-- Inverse image along a composite is canonically isomorphic to iterated inverse image. -/
def inverseImageCompIso {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (abelianInverseImageExact C J (ψ ≫ φ)).obj ≅
      (abelianInverseImageExact C J ψ).obj ⋙ (abelianInverseImageExact C J φ).obj :=
  (Functor.sheafPullbackComp' (J l).toGrothendieck (J m).toGrothendieck
    (J n).toGrothendieck (C.map ψ).toFunctor (C.map φ).toFunctor
    (A := AddCommGrpCat.{w}) (map_comp_toFunctor C ψ φ)).symm

/-- The canonical pullbacks of a diagram of site morphisms form an anchored
inverse-image context with coherent unit and composition comparisons. -/
instance inverseImageContext :
    IsInverseImageContext (fun n ↦ (J n).toGrothendieck)
      (fun φ ↦ (abelianInverseImageExact C J φ).obj)
      (inverseImageCompIso C J) := sorry

end AbelianDerived

/-- Canonical derived restriction transitions respect composition of simplex operators. -/
theorem toDerivedSystem_map_comp
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    derivedTransition C J (ψ ≫ φ) K =
      (derivedInverseImageCompIso (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ (abelianInverseImageExact C J φ).obj) ψ φ
        (AbelianDerived.inverseImageCompIso C J ψ φ)).hom.app ((derivedRestrict C J l).obj K) ≫
      ((abelianInverseImageExact C J φ).obj).mapDerivedCategory.map
        (derivedTransition C J ψ K) ≫ derivedTransition C J φ K := sorry

/-- An object of the total derived category determines its system of canonical restrictions. -/
def toDerivedSystem (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) :
    DerivedSystem (fun n ↦ (J n).toGrothendieck)
      (fun φ ↦ (abelianInverseImageExact C J φ).obj)
      (AbelianDerived.inverseImageCompIso C J) :=
  DerivedSystem.of inferInstance (fun n ↦ (derivedRestrict C J n).obj K)
    (fun φ ↦ derivedTransition C J φ K) (toDerivedSystem_map_comp C J K)

/-- The degree object of the restriction system is the canonical derived restriction. -/
theorem toDerivedSystem_obj
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})) (n : SimplexCategory) :
    (toDerivedSystem C J K).obj n = (derivedRestrict C J n).obj K := sorry

/-- The transition of the restriction system is the canonical derived comparison. -/
theorem toDerivedSystem_map
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (toDerivedSystem C J K).map φ = derivedTransition C J φ K := sorry

/-- The restriction system of a cartesian total derived object is cartesian. -/
theorem toDerivedSystem_isCartesian
    (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
    [AbelianDerived.IsCartesian C J K] :
    DerivedSystem.IsCartesian (toDerivedSystem C J K) := sorry

/-- Derived restrictions of a total morphism commute with the canonical transitions. -/
theorem toDerivedSystemMap_naturality
    {K K' : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})} (f : K ⟶ K')
    {m n : SimplexCategory} (φ : m ⟶ n) :
    derivedTransition C J φ K ≫ (derivedRestrict C J n).map f =
      ((abelianInverseImageExact C J φ).obj).mapDerivedCategory.map
        ((derivedRestrict C J m).map f) ≫ derivedTransition C J φ K' := sorry

/-- A morphism of total derived objects induces the family of its derived restrictions. -/
def toDerivedSystemMap
    {K K' : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})} (f : K ⟶ K') :
    DerivedSystem.Hom (toDerivedSystem C J K) (toDerivedSystem C J K') :=
  DerivedSystem.homMk (fun n ↦ (derivedRestrict C J n).map f)
    (toDerivedSystemMap_naturality C J f)

/-- The components of the induced system morphism are the derived restrictions of the morphism. -/
theorem toDerivedSystemMap_app
    {K K' : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})}
    (f : K ⟶ K') (n : SimplexCategory) :
    (toDerivedSystemMap C J f).app n = (derivedRestrict C J n).map f := sorry

end CategoryTheory.SimplicialSites
