module

public import stacks_project.Chap92.Definition_92_22_1_Cotangent
public import Mathlib.Algebra.Homology.Additive
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction

/-!
# Functoriality of sheaf cotangent complexes over a fixed base

A morphism of commutative algebra sheaves over a fixed ring sheaf induces a canonical
cochain map of cotangent complexes after extension of scalars along the underlying
ring-sheaf morphism.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicTopology
open HomologicalComplex
open ComplexShape
open SheafOfModules.RingedSite
open scoped Simplicial

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]

/-- The morphism of standard-resolution terms induced by a morphism of algebras over a
fixed base ring sheaf. -/
def standardTermMap {A : Sheaf J CommRingCat.{u}} {B B' : Under A} (h : B ⟶ B')
    (n : SimplexCategoryᵒᵖ) :
    standardTerm A B n ⟶ standardTerm A B' n :=
  ((Adjunction.SimplicialResolution.eval (freeForgetAdjunction A)).map h).left.app n

/-- Unfolding of `standardTermMap` as the degree-`n` component of the simplicial resolution
functor. -/
theorem standardTermMap_eq {A : Sheaf J CommRingCat.{u}} {B B' : Under A} (h : B ⟶ B')
    (n : SimplexCategoryᵒᵖ) :
    standardTermMap h n =
      ((Adjunction.SimplicialResolution.eval (freeForgetAdjunction A)).map h).left.app n :=
  sorry

/-- Augmentations of standard-resolution terms form a commutative square with a morphism of
algebras over a fixed base. -/
theorem standardTermMap_comp_augmentation {A : Sheaf J CommRingCat.{u}}
    {B B' : Under A} (h : B ⟶ B') (n : SimplexCategoryᵒᵖ) :
    (standardTermMap h n).right ≫ standardAugmentation A B' n =
      standardAugmentation A B n ≫ h.right :=
  sorry

/-- Forgetting commutativity identifies the two successive restriction paths of a morphism of
standard-resolution terms. -/
theorem standardTermMap_comp_augmentation_ringSheaf {A : Sheaf J CommRingCat.{u}}
    {B B' : Under A} (h : B ⟶ B') (n : SimplexCategoryᵒᵖ) :
    ringSheafMap (standardAugmentation A B n ≫ h.right) =
      ringSheafMap (standardTermMap h n).right ≫
        ringSheafMap (standardAugmentation A B' n) :=
  sorry

/-- The square of structure maps of standard-resolution terms over a fixed base. -/
theorem standardTermMap_w {A : Sheaf J CommRingCat.{u}} {B B' : Under A}
    (h : B ⟶ B') (n : SimplexCategoryᵒᵖ) :
    (standardTerm A B n).hom ≫ (standardTermMap h n).right =
      (standardTerm A B' n).hom :=
  sorry

/-- The map of relative differentials of standard-resolution terms induced by a morphism of
algebras over a fixed base. -/
def standardDifferentialsMap {A : Sheaf J CommRingCat.{u}} {B B' : Under A}
    (h : B ⟶ B') (n : SimplexCategoryᵒᵖ) :
    relativeDifferentials (standardTerm A B n).hom ⟶
      (restrictionAlong (standardTermMap h n).right).obj
        (relativeDifferentials (standardTerm A B' n).hom) :=
  RelativeDifferentials.map
    ⟨(Category.id_comp (standardTerm A B' n).hom).trans (standardTermMap_w h n).symm⟩

/-- Unfolding of `standardDifferentialsMap` as `RelativeDifferentials.map` of the structure-map
square. -/
theorem standardDifferentialsMap_eq {A : Sheaf J CommRingCat.{u}} {B B' : Under A}
    (h : B ⟶ B') (n : SimplexCategoryᵒᵖ) :
    standardDifferentialsMap h n =
      RelativeDifferentials.map
        ⟨(Category.id_comp (standardTerm A B' n).hom).trans (standardTermMap_w h n).symm⟩ :=
  sorry

/-- The `B`-module map underlying a square map of simplicial cotangent terms, before extension
of scalars along the target ring-sheaf morphism. -/
def standardBModuleMap {A : Sheaf J CommRingCat.{u}} {B B' : Under A} (h : B ⟶ B')
    (n : SimplexCategoryᵒᵖ) :
    (simplicialModule A B).obj n ⟶
      (restrictionAlong h.right).obj ((simplicialModule A B').obj n) :=
  ((extendRestrictAdj (standardAugmentation A B n)).homEquiv _ _).symm
    (standardDifferentialsMap h n ≫
      (restrictionAlong (standardTermMap h n).right).map
        ((extendRestrictAdj (standardAugmentation A B' n)).unit.app _) ≫
      (SheafOfModules.Restriction.compIso'
          (ringSheafMap (standardTermMap h n).right)
          (ringSheafMap (standardAugmentation A B' n))
          (ringSheafMap (standardAugmentation A B n ≫ h.right))
          (standardTermMap_comp_augmentation_ringSheaf h n)).hom.app _ ≫
      (SheafOfModules.Restriction.compIso'
          (ringSheafMap (standardAugmentation A B n))
          (ringSheafMap h.right)
          (ringSheafMap (standardAugmentation A B n ≫ h.right))
          (ringSheafMap_comp (standardAugmentation A B n) h.right)).inv.app _)

/-- Degreewise map of standard-resolution simplicial modules after extending scalars along a
morphism of algebras over a fixed base. -/
def simplicialMap {A : Sheaf J CommRingCat.{u}} {B B' : Under A} (h : B ⟶ B')
    (n : SimplexCategoryᵒᵖ) :
    (extendAlong h.right).obj ((simplicialModule A B).obj n) ⟶
      (simplicialModule A B').obj n :=
  ((extendRestrictAdj h.right).homEquiv _ _).symm (standardBModuleMap h n)

/-- Unfolding of `simplicialMap` through the extension-restriction adjunction. -/
theorem simplicialMap_eq {A : Sheaf J CommRingCat.{u}} {B B' : Under A} (h : B ⟶ B')
    (n : SimplexCategoryᵒᵖ) :
    simplicialMap h n =
      ((extendRestrictAdj h.right).homEquiv _ _).symm (standardBModuleMap h n) :=
  sorry

/-- The cochain map of sheaf cotangent complexes induced by a morphism of algebras over a
fixed base ring sheaf. -/
def map {A : Sheaf J CommRingCat.{u}} {B B' : Under A} (h : B ⟶ B') :
    ((extendAlong h.right).mapHomologicalComplex (up ℤ)).obj (obj A B) ⟶ obj A B' where
  f i :=
    match hr : embeddingDownNat.r i with
    | some n =>
        (extendAlong h.right).map
            (extendXIso
              ((alternatingFaceMapComplex (SheafOfModules (ringSheaf J B.right))).obj
                (simplicialModule A B))
              embeddingDownNat (embeddingDownNat.f_eq_of_r_eq_some hr)).hom ≫
          simplicialMap h (op ⦋n⦌) ≫
          (extendXIso
              ((alternatingFaceMapComplex (SheafOfModules (ringSheaf J B'.right))).obj
                (simplicialModule A B'))
              embeddingDownNat (embeddingDownNat.f_eq_of_r_eq_some hr)).inv
    | none => 0
  comm' := sorry

end SheafOfModules.RingedSite.CotangentComplex
