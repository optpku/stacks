/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
public import Mathlib.Algebra.Homology.Additive
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.CategoryTheory.Endofunctor.Iteration.Natural
public import Mathlib.CategoryTheory.CommSq

/-!
# Functoriality of sheaf cotangent complexes

Morphisms of commutative algebra sheaves induce canonical maps of standard resolutions
and cotangent complexes. Fixed-base morphisms extend scalars along the underlying ring map;
change of base with fixed target induces a map between the corresponding cotangent complexes.
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
  (standardTermMap h n).w

/-- The map of relative differentials of standard-resolution terms induced by a morphism of
algebras over a fixed base. -/
def standardDifferentialsMap {A : Sheaf J CommRingCat.{u}} {B B' : Under A}
    (h : B ⟶ B') (n : SimplexCategoryᵒᵖ) :
    relativeDifferentials (standardTerm A B n).hom ⟶
      (restrictionAlong (standardTermMap h n).right).obj
        (relativeDifferentials (standardTerm A B' n).hom) :=
  RelativeDifferentials.map
    ⟨(Category.id_comp (standardTerm A B' n).hom).trans (standardTermMap_w h n).symm⟩

/-- The `B`-module map underlying a square map of simplicial cotangent terms, before extension
of scalars along the target ring-sheaf morphism. -/
def standardBModuleMap {A : Sheaf J CommRingCat.{u}} {B B' : Under A} (h : B ⟶ B')
    (n : SimplexCategoryᵒᵖ) :
    (simplicialModule A B).obj n ⟶
      (restrictionAlong h.right).obj ((simplicialModule A B').obj n) :=
  ((ChangeOfRings.extendRestrictAdjunction
      (ringSheafMap (standardAugmentation A B n))).homEquiv _ _).symm
    (standardDifferentialsMap h n ≫
      (restrictionAlong (standardTermMap h n).right).map
        ((ChangeOfRings.extendRestrictAdjunction
          (ringSheafMap (standardAugmentation A B' n))).unit.app _) ≫
      (SheafOfModules.Restriction.compIso'
          (ringSheafMap (standardTermMap h n).right)
          (ringSheafMap (standardAugmentation A B' n))
          (ringSheafMap (standardAugmentation A B n ≫ h.right))
          (standardTermMap_comp_augmentation_ringSheaf h n)).hom.app _ ≫
      (SheafOfModules.Restriction.compIso'
          (ringSheafMap (standardAugmentation A B n))
          (ringSheafMap h.right)
          (ringSheafMap (standardAugmentation A B n ≫ h.right))
          (by rfl)).inv.app _)

/-- Degreewise map of standard-resolution simplicial modules after extending scalars along a
morphism of algebras over a fixed base. -/
def simplicialMap {A : Sheaf J CommRingCat.{u}} {B B' : Under A} (h : B ⟶ B')
    (n : SimplexCategoryᵒᵖ) :
    (ChangeOfRings.extendScalars (ringSheafMap h.right)).obj ((simplicialModule A B).obj n) ⟶
      (simplicialModule A B').obj n :=
  ((ChangeOfRings.extendRestrictAdjunction (ringSheafMap h.right)).homEquiv _ _).symm
    (standardBModuleMap h n)

/-- The cochain map of sheaf cotangent complexes induced by a morphism of algebras over a
fixed base ring sheaf. -/
def map {A : Sheaf J CommRingCat.{u}} {B B' : Under A} (h : B ⟶ B') :
    ((ChangeOfRings.extendScalars (ringSheafMap h.right)).mapHomologicalComplex (up ℤ)).obj
      (obj A B) ⟶ obj A B' where
  f i :=
    match hr : embeddingDownNat.r i with
    | some n =>
        (ChangeOfRings.extendScalars (ringSheafMap h.right)).map
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

/-- The free-forgetful comonad endofunctor on algebras under a fixed ring sheaf. -/
def freeForgetEndo (A : Sheaf J CommRingCat.{u}) : Under A ⥤ Under A :=
  (freeForgetAdjunction A).toComonad.toFunctor

/-- A cross-base map between one free-forgetful step is specified before iterating it. -/
def freeForgetRightHom {A A' : Sheaf J CommRingCat.{u}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right) :
    ((freeForgetEndo A).obj B).right ⟶ ((freeForgetEndo A').obj B').right :=
  (((freeForgetAdjunction A).homEquiv
    ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj B.right)
    (Under.mk (α ≫ ((freeForgetEndo A').obj B').hom))).symm
      (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map β) ≫
        (freeForgetAdjunction A').unit.app
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj B'.right))).right

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
in
/-- The one-step map extends the specified homomorphism on base sheaves. -/
theorem freeForgetRightHom_base {A A' : Sheaf J CommRingCat.{u}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right) :
    ((freeForgetEndo A).obj B).hom ≫
        freeForgetRightHom (B := B) (B' := B') α β =
      α ≫ ((freeForgetEndo A').obj B').hom := sorry

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
in
/-- On generators, the one-step map is the specified map followed by the target free unit. -/
theorem freeForgetRightHom_unit {A A' : Sheaf J CommRingCat.{u}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right) :
    (freeForgetAdjunction A).unit.app
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj B.right) ≫
      (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map
        (freeForgetRightHom (B := B) (B' := B') α β) =
      (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map β ≫
        (freeForgetAdjunction A').unit.app
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj B'.right) := sorry

/-- The iterated ring-sheaf map of standard-resolution terms induced by a map of bases and
resolved algebras. -/
def iterateRightHom {A A' : Sheaf J CommRingCat.{u}} {B : Under A} {B' : Under A'}
    (α : A ⟶ A') (β : B.right ⟶ B'.right) :
    (n : ℕ) →
      ((Endofunctor.iterate (freeForgetEndo A) n).obj B).right ⟶
        ((Endofunctor.iterate (freeForgetEndo A') n).obj B').right
  | 0 => β
  | n + 1 =>
      freeForgetRightHom
        (B := (Endofunctor.iterate (freeForgetEndo A) n).obj B)
        (B' := (Endofunctor.iterate (freeForgetEndo A') n).obj B')
        α (iterateRightHom (A := A) (A' := A') (B := B) (B' := B') α β n)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
in
/-- The zeroth iterated cross-base map is the original underlying map. -/
@[simp]
theorem iterateRightHom_zero {A A' : Sheaf J CommRingCat.{u}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right) :
    iterateRightHom (A := A) (A' := A') (B := B) (B' := B') α β 0 = β := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
in
/-- The successor iterated map applies the same specified free-algebra step. -/
@[simp]
theorem iterateRightHom_succ {A A' : Sheaf J CommRingCat.{u}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right) (n : ℕ) :
    iterateRightHom (A := A) (A' := A') (B := B) (B' := B') α β (n + 1) =
      freeForgetRightHom
        (B := (Endofunctor.iterate (freeForgetEndo A) n).obj B)
        (B' := (Endofunctor.iterate (freeForgetEndo A') n).obj B')
        α (iterateRightHom (A := A) (A' := A') (B := B) (B' := B') α β n) := rfl

/-- The ring-sheaf map of standard-resolution terms induced by a map of bases and resolved
algebras. -/
irreducible_def standardTermRightHom {A A' : Sheaf J CommRingCat.{u}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (n : SimplexCategoryᵒᵖ) :
    (standardTerm A B n).right ⟶ (standardTerm A' B' n).right :=
  iterateRightHom (A := A) (A' := A') (B := B) (B' := B') α β (n.unop.len + 1)

/-- Structure maps of standard-resolution terms form a commutative square with the induced
termwise ring-sheaf maps. -/
theorem standardTermRightHom_square {A A' : Sheaf J CommRingCat.{u}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    α ≫ (standardTerm A' B' n).hom =
      (standardTerm A B n).hom ≫ standardTermRightHom α β n :=
  sorry

/-- Augmentations of standard-resolution terms form a commutative square with the induced
termwise ring-sheaf maps. -/
theorem standardTermRightHom_comp_augmentation {A A' : Sheaf J CommRingCat.{u}}
    {B : Under A} {B' : Under A'} (α : A ⟶ A') (β : B.right ⟶ B'.right)
    (hα : α ≫ B'.hom = B.hom ≫ β) (n : SimplexCategoryᵒᵖ) :
    ringSheafMap (standardAugmentation A B n ≫ β) =
      ringSheafMap (standardTermRightHom α β n) ≫
        ringSheafMap (standardAugmentation A' B' n) :=
  sorry

/-- The identity on `C` is compatible with change of base along `φ` for the composite `φ ≫ ψ`. -/
private theorem toRelative_w {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    φ ≫ ψ = (φ ≫ ψ) ≫ 𝟙 C := by
  simp only [Category.comp_id]

/-- The commutative square of structure maps used by the second transitivity map. -/
private theorem relativeTermSquare {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    CommSq φ (standardTerm A (Under.mk (φ ≫ ψ)) n).hom
      (standardTerm B (Under.mk ψ) n).hom (standardTermRightHom (B := Under.mk (φ ≫ ψ)) (B' := Under.mk ψ) φ (𝟙 C) n) :=
  ⟨standardTermRightHom_square
    (B := Under.mk (φ ≫ ψ)) (B' := Under.mk ψ)
    φ (𝟙 C) (toRelative_w φ ψ) n⟩

/-- Termwise base-change of relative differentials along `relativeTermSquare`. -/
private def relativeDifferentialsTermMap {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    relativeDifferentials (standardTerm A (Under.mk (φ ≫ ψ)) n).hom ⟶
      (restrictionAlong (standardTermRightHom (B := Under.mk (φ ≫ ψ)) (B' := Under.mk ψ) φ (𝟙 C) n)).obj
        (relativeDifferentials (standardTerm B (Under.mk ψ) n).hom) :=
  RelativeDifferentials.map (relativeTermSquare φ ψ n)

/-- Ring-level augmentation compatibility for `relativeTermSquare`. -/
private theorem relativeAugmentation_comp_ring {A B C : Sheaf J CommRingCat.{u}}
    (φ : A ⟶ B) (ψ : B ⟶ C) (n : SimplexCategoryᵒᵖ) :
    ringSheafMap (standardAugmentation A (Under.mk (φ ≫ ψ)) n) =
      ringSheafMap (standardTermRightHom (B := Under.mk (φ ≫ ψ)) (B' := Under.mk ψ) φ (𝟙 C) n) ≫
        ringSheafMap (standardAugmentation B (Under.mk ψ) n) := by
  have h := standardTermRightHom_comp_augmentation
    (B := Under.mk (φ ≫ ψ)) (B' := Under.mk ψ)
    φ (𝟙 C) (toRelative_w φ ψ) n
  change ringSheafMap (standardAugmentation A (Under.mk (φ ≫ ψ)) n ≫ 𝟙 C) = _ at h
  erw [Category.comp_id] at h
  exact h

/-- The map on relative differentials followed by the target augmentation unit and the
comparison of successive restrictions. -/
private def relativeRestrictedMap {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    relativeDifferentials (standardTerm A (Under.mk (φ ≫ ψ)) n).hom ⟶
      (restrictionAlong (standardAugmentation A (Under.mk (φ ≫ ψ)) n)).obj
        ((simplicialModule B (Under.mk ψ)).obj n) :=
  relativeDifferentialsTermMap φ ψ n ≫
    (restrictionAlong (standardTermRightHom (B := Under.mk (φ ≫ ψ)) (B' := Under.mk ψ) φ (𝟙 C) n)).map
      ((ChangeOfRings.extendRestrictAdjunction
        (ringSheafMap (standardAugmentation B (Under.mk ψ) n))).unit.app
        (relativeDifferentials (standardTerm B (Under.mk ψ) n).hom)) ≫
    (SheafOfModules.Restriction.compIso'
      (ringSheafMap (standardTermRightHom (B := Under.mk (φ ≫ ψ)) (B' := Under.mk ψ) φ (𝟙 C) n))
      (ringSheafMap (standardAugmentation B (Under.mk ψ) n))
      (ringSheafMap (standardAugmentation A (Under.mk (φ ≫ ψ)) n))
      (relativeAugmentation_comp_ring φ ψ n)).hom.app
        ((simplicialModule B (Under.mk ψ)).obj n)

/-- Degreewise second transitivity map of simplicial cotangent modules, changing the base
ring sheaf while keeping the total algebra `C`. -/
private def relativeSimplicialMap {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    (simplicialModule A (Under.mk (φ ≫ ψ))).obj n ⟶
      (simplicialModule B (Under.mk ψ)).obj n :=
  ((ChangeOfRings.extendRestrictAdjunction
      (ringSheafMap (standardAugmentation A (Under.mk (φ ≫ ψ)) n))).homEquiv _ _).symm
    (relativeRestrictedMap φ ψ n)

/-- The unextended second transitivity map `L(φ ≫ ψ) ⟶ L(ψ)`, induced by base change of
relative differentials along `φ`. -/
@[no_expose]
def toRelativeMapCochain {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C) :
    L(φ ≫ ψ) ⟶ L(ψ) where
  f i :=
    match h : embeddingDownNat.r i with
    | some n =>
        (extendXIso
            ((alternatingFaceMapComplex (SheafOfModules (ringSheaf J C))).obj
              (simplicialModule A (Under.mk (φ ≫ ψ))))
            embeddingDownNat
            (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).hom ≫
          relativeSimplicialMap φ ψ (op ⦋n⦌) ≫
          (extendXIso
              ((alternatingFaceMapComplex (SheafOfModules (ringSheaf J C))).obj
                (simplicialModule B (Under.mk ψ)))
              embeddingDownNat
              (Embedding.f_eq_of_r_eq_some (e := embeddingDownNat) h)).inv
    | none => 0
  comm' := sorry

end SheafOfModules.RingedSite.CotangentComplex
