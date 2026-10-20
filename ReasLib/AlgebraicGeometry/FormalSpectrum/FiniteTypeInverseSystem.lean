/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.AlgebraicGeometry.FormalSpectrum.WeakIdeal

/-!
# Finite-type inverse systems over weak-ideal quotients

The category `C` of inverse systems `(B_I)` of finite-type `A ⧸ I`-algebras,
indexed by weak ideals of definition of a topological ring `A`, with
transition isomorphisms `B_J ⧸ I B_J ≅ B_I`, is the full subcategory of
`Under (quotStages A)` on `IsFiniteTypeInverseSystem`.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The quotient factor associated to an identity is the identity ring map. -/
theorem quotStages_map_id (A : Type u) [CommRing A] [TopologicalSpace A]
    (I : (WeakIdealOfDefinition A)ᵒᵖ) :
    CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom (𝟙 I).unop)) =
      𝟙 (CommRingCat.of (A ⧸ I.unop.ideal)) :=
  sorry

/-- Quotient factor maps preserve composition in the opposite weak-ideal index. -/
theorem quotStages_map_comp (A : Type u) [CommRing A] [TopologicalSpace A]
    {I J K : (WeakIdealOfDefinition A)ᵒᵖ} (f : I ⟶ J) (g : J ⟶ K) :
    CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom (f ≫ g).unop)) =
      CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom f.unop)) ≫
        CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom g.unop)) :=
  sorry

/-- The inverse system of quotients `A ⧸ I` as `I` runs over weak ideals of
definition of `A`. A morphism `I ⟶ J` in the opposite preorder (equivalently
`I.unop.ideal ≤ J.unop.ideal`) is sent to `Ideal.Quotient.factor`. -/
def quotStages (A : Type u) [CommRing A] [TopologicalSpace A] :
    (WeakIdealOfDefinition A)ᵒᵖ ⥤ CommRingCat.{u} where
  obj I := .of (A ⧸ I.unop.ideal)
  map {I J} f :=
    CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom f.unop))
  map_id := quotStages_map_id A
  map_comp := quotStages_map_comp A

/-- Objects of `quotStages A` are the quotient rings `A ⧸ I`. -/
theorem quotStages_obj {A : Type u} [CommRing A] [TopologicalSpace A]
    (I : (WeakIdealOfDefinition A)ᵒᵖ) :
    (quotStages A).obj I = .of (A ⧸ I.unop.ideal) :=
  rfl

/-- Morphisms of `quotStages A` are the canonical quotient factorizations. -/
theorem quotStages_map {A : Type u} [CommRing A] [TopologicalSpace A]
    {I J : (WeakIdealOfDefinition A)ᵒᵖ} (f : I ⟶ J) :
    (quotStages A).map f =
      CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom f.unop)) :=
  rfl

/-- The `A ⧸ I`-algebra structure on a stage of an object of
`Under (quotStages A)`, taken from the under-morphism at `I`. -/
instance algebra_underQuotStages {A : Type u} [CommRing A] [TopologicalSpace A]
    (B : Under (quotStages A)) (I : (WeakIdealOfDefinition A)ᵒᵖ) :
    Algebra (A ⧸ I.unop.ideal) (B.right.obj I) :=
  (B.hom.app I).hom.toAlgebra

/-- The algebra map of `algebra_underQuotStages` is the under-morphism at `I`. -/
theorem algebra_underQuotStages_algebraMap {A : Type u} [CommRing A]
    [TopologicalSpace A] (B : Under (quotStages A))
    (I : (WeakIdealOfDefinition A)ᵒᵖ) :
    algebraMap (A ⧸ I.unop.ideal) (B.right.obj I) = (B.hom.app I).hom :=
  rfl

/-- The ideal defining a stage quotient is killed by its transition map. -/
theorem stageQuotientHom_ker {A : Type u} [CommRing A] [TopologicalSpace A]
    (B : Under (quotStages A)) {I J : (WeakIdealOfDefinition A)ᵒᵖ} (f : I ⟶ J) :
    J.unop.ideal.map
        ((B.hom.app I).hom.comp (Ideal.Quotient.mk I.unop.ideal)) ≤
      RingHom.ker (B.right.map f).hom :=
  sorry

/-- The canonical comparison `B_I ⧸ J.unop.ideal • B_I ⟶ B_J` induced by a
transition map of an object of `Under (quotStages A)`. -/
def stageQuotientHom {A : Type u} [CommRing A] [TopologicalSpace A]
    (B : Under (quotStages A)) {I J : (WeakIdealOfDefinition A)ᵒᵖ} (f : I ⟶ J) :
    CommRingCat.of
        (B.right.obj I ⧸
          J.unop.ideal.map
            ((B.hom.app I).hom.comp (Ideal.Quotient.mk I.unop.ideal))) ⟶
      B.right.obj J :=
  CommRingCat.ofHom (Ideal.Quotient.lift _ (B.right.map f).hom (stageQuotientHom_ker B f))

/-- `stageQuotientHom` sends the class of a stage element to its image under
the inverse-system transition. -/
theorem stageQuotientHom_apply {A : Type u} [CommRing A] [TopologicalSpace A]
    (B : Under (quotStages A)) {I J : (WeakIdealOfDefinition A)ᵒᵖ} (f : I ⟶ J)
    (x : B.right.obj I) :
    (stageQuotientHom B f).hom (Ideal.Quotient.mk _ x) = (B.right.map f).hom x :=
  rfl

/-- An object of `Under (quotStages A)` is a finite-type inverse system when
each stage is of finite type over `A ⧸ I` and each comparison
`B_I ⧸ J.unop.ideal • B_I ⟶ B_J` is an isomorphism. -/
class IsFiniteTypeInverseSystem {A : Type u} [CommRing A] [TopologicalSpace A]
    (B : Under (quotStages A)) : Prop where
  /-- Each stage `B_I` is a finite-type `A ⧸ I`-algebra. -/
  finiteType : ∀ I : (WeakIdealOfDefinition A)ᵒᵖ,
    Algebra.FiniteType (A ⧸ I.unop.ideal) (B.right.obj I)
  /-- Each comparison `B_I ⧸ J.unop.ideal • B_I ⟶ B_J` is an isomorphism. -/
  stageIso : ∀ {I J : (WeakIdealOfDefinition A)ᵒᵖ} (f : I ⟶ J),
    IsIso (stageQuotientHom B f)

/-- The identity system `A ⧸ I` is a finite-type inverse system. -/
instance IsFiniteTypeInverseSystem.instQuotStages {A : Type u} [CommRing A]
    [TopologicalSpace A] :
    IsFiniteTypeInverseSystem (Under.mk (𝟙 (quotStages A))) :=
  sorry

/-- A finite-type inverse system has finite-type stages and isomorphic
stage comparisons. -/
theorem IsFiniteTypeInverseSystem.spec {A : Type u} [CommRing A]
    [TopologicalSpace A] (B : Under (quotStages A))
    [h : IsFiniteTypeInverseSystem B] :
    (∀ I : (WeakIdealOfDefinition A)ᵒᵖ,
        Algebra.FiniteType (A ⧸ I.unop.ideal) (B.right.obj I)) ∧
      ∀ {I J : (WeakIdealOfDefinition A)ᵒᵖ} (f : I ⟶ J),
        IsIso (stageQuotientHom B f) :=
  ⟨h.finiteType, h.stageIso⟩

/-- Membership in `IsFiniteTypeInverseSystem` is equivalent to finite-type
stages together with isomorphic stage comparisons. -/
theorem IsFiniteTypeInverseSystem.iff {A : Type u} [CommRing A]
    [TopologicalSpace A] (B : Under (quotStages A)) :
    IsFiniteTypeInverseSystem B ↔
      (∀ I : (WeakIdealOfDefinition A)ᵒᵖ,
          Algebra.FiniteType (A ⧸ I.unop.ideal) (B.right.obj I)) ∧
        ∀ {I J : (WeakIdealOfDefinition A)ᵒᵖ} (f : I ⟶ J),
          IsIso (stageQuotientHom B f) :=
  ⟨fun h ↦ ⟨h.finiteType, h.stageIso⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- The category of inverse systems of finite-type `A ⧸ I`-algebras with
transition isomorphisms `B_J ⧸ I B_J ≅ B_I`. -/
abbrev FiniteTypeInverseSystem (A : Type u) [CommRing A] [TopologicalSpace A] :=
  ObjectProperty.FullSubcategory
    fun B : Under (quotStages A) ↦ IsFiniteTypeInverseSystem B

/-- `FiniteTypeInverseSystem A` is the full subcategory of `Under (quotStages A)`
on finite-type inverse systems. -/
theorem FiniteTypeInverseSystem_def (A : Type u) [CommRing A]
    [TopologicalSpace A] :
    FiniteTypeInverseSystem A =
      ObjectProperty.FullSubcategory
        fun B : Under (quotStages A) ↦ IsFiniteTypeInverseSystem B :=
  rfl

/-- Construct an object of `FiniteTypeInverseSystem A` from an under-object
satisfying `IsFiniteTypeInverseSystem`. -/
def FiniteTypeInverseSystem.mk {A : Type u} [CommRing A] [TopologicalSpace A]
    (B : Under (quotStages A)) [IsFiniteTypeInverseSystem B] :
    FiniteTypeInverseSystem A :=
  ⟨B, inferInstance⟩

/-- The underlying under-object of `FiniteTypeInverseSystem.mk B` is `B`. -/
theorem FiniteTypeInverseSystem.mk_obj {A : Type u} [CommRing A]
    [TopologicalSpace A] (B : Under (quotStages A))
    [IsFiniteTypeInverseSystem B] :
    (FiniteTypeInverseSystem.mk B).obj = B :=
  rfl

/-- The underlying inverse-system functor of `FiniteTypeInverseSystem.mk B` is
the right component of `B`. -/
theorem FiniteTypeInverseSystem.mk_right {A : Type u} [CommRing A]
    [TopologicalSpace A] (B : Under (quotStages A))
    [IsFiniteTypeInverseSystem B] :
    (FiniteTypeInverseSystem.mk B).obj.right = B.right :=
  rfl

end AlgebraicGeometry.AffineFormalAlgebraicSpace
