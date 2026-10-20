/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Evaluation on Cosimplicial Objects

This module gives the simplicial and derived evaluation constructions attached to a
cosimplicial object, together with the pointlike mapping-space condition used by descent and
cohomological descent arguments.
-/

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open ComplexShape
open Opposite
open SSet.stdSimplex (isTerminalObj₀)
open scoped CategoryTheory Simplicial

noncomputable section

universe u v w u' v'

namespace CategoryTheory

namespace Functor

variable {C : Type u} [Category.{v} C]
variable {C' : Type u'} [Category.{v'} C']

/-- Reindex a cosimplicial object along `u : C' ⥤ C`. -/
@[stacks 08QA "cosimplicial reindexing"]
abbrev mapCosimplicialObject (u : C' ⥤ C) (Ubullet : CosimplicialObject C') :
    CosimplicialObject C :=
  ((CosimplicialObject.whiskering C' C).obj u).obj Ubullet

end Functor

namespace CosimplicialObject

namespace Pointlike

variable {C : Type u} [Category.{v} C]

/-- The simplicial set of morphisms from the cosimplicial object `Ubullet` to `U`. -/
@[stacks 08Q9 "cosimplicial mapping simplicial set"]
abbrev homSSet (Ubullet : CosimplicialObject C) (U : C) :
    SSet.{v} :=
  ((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ (Type v)).obj
      ((cosimplicialSimplicialEquiv C).functor.obj (op Ubullet))).obj
    (yoneda.obj U)

/-- Every mapping simplicial set from `Ubullet` is homotopy equivalent to `Δ[0]`. -/
@[stacks 08Q9 "pointlike cosimplicial mapping spaces"]
def HasHomSpaces (Ubullet : CosimplicialObject C) : Prop :=
  ∀ U : C,
    Nonempty (SimplicialObject.HomotopyEquiv
      (homSSet Ubullet U)
      (Δ[0] : SSet))

/-- The pointlike mapping-space condition is equivalent to the canonical map to `Δ[0]` being a
simplicial homotopy equivalence. -/
@[stacks 08Q9 "pointlike mapping-space criterion"]
theorem hasHomSpaces_iff
    (Ubullet : CosimplicialObject C) :
    HasHomSpaces Ubullet ↔
      ∀ U : C,
        SimplicialObject.IsHomotopyEquivalence
          (isTerminalObj₀.from (homSSet Ubullet U)) := sorry

end Pointlike

namespace Evaluation

variable {C : Type u} [Category.{v} C]
variable (A : Type w) [Category A] [Abelian A]

/-- Evaluation of an `A`-valued presheaf on a cosimplicial object, as a simplicial object of
`A`. -/
@[stacks 08Q9 "cosimplicial evaluation as a simplicial object"]
abbrev simplicial
    (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ A) ⥤ SimplicialObject A :=
  (Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ A).obj
    ((cosimplicialSimplicialEquiv C).functor.obj (op Ubullet))

section ColimitAugmentation

variable [HasColimitsOfShape Cᵒᵖ A]

/-- Compatibility of the colimit cocone maps with the simplicial operators of cosimplicial
evaluation. -/
@[stacks 08Q9 "cosimplicial evaluation colimit-cocone compatibility"]
theorem colimitAugmentationApp_naturality
    (Ubullet : CosimplicialObject C) (F : Cᵒᵖ ⥤ A)
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    ((simplicial A Ubullet).obj F).map f ≫
        colimit.ι F (op (Ubullet.obj Δ'.unop)) =
      colimit.ι F (op (Ubullet.obj Δ.unop)) ≫
        ((SimplicialObject.const A).obj
          ((colim : (Cᵒᵖ ⥤ A) ⥤ A).obj F)).map f := sorry

/-- The canonical augmentation from cosimplicial evaluation of `F` to the constant simplicial
object on `colim.obj F`. Its degreewise maps are the colimit cocone maps. -/
@[stacks 08Q9 "cosimplicial evaluation colimit augmentation component"]
def colimitAugmentationApp
    (Ubullet : CosimplicialObject C) (F : Cᵒᵖ ⥤ A) :
    (simplicial A Ubullet).obj F ⟶
      (SimplicialObject.const A).obj ((colim : (Cᵒᵖ ⥤ A) ⥤ A).obj F) where
  app Δ := colimit.ι F (op (Ubullet.obj Δ.unop))
  naturality _ _ f := colimitAugmentationApp_naturality A Ubullet F f

/-- Naturality of the cosimplicial-evaluation augmentation in the coefficient presheaf. -/
@[stacks 08Q9 "cosimplicial evaluation colimit augmentation naturality"]
theorem colimitAugmentation_naturality
    (Ubullet : CosimplicialObject C) {F G : Cᵒᵖ ⥤ A} (t : F ⟶ G) :
    (simplicial A Ubullet).map t ≫ colimitAugmentationApp A Ubullet G =
      colimitAugmentationApp A Ubullet F ≫
        (SimplicialObject.const A).map ((colim : (Cᵒᵖ ⥤ A) ⥤ A).map t) := sorry

/-- The canonical natural augmentation from cosimplicial evaluation to the constant simplicial
object on the presheaf colimit, induced degreewise by the colimit cocone. -/
@[stacks 08Q9 "canonical cosimplicial evaluation augmentation"]
def colimitAugmentation (Ubullet : CosimplicialObject C) :
    simplicial A Ubullet ⟶
      (colim : (Cᵒᵖ ⥤ A) ⥤ A) ⋙ SimplicialObject.const A where
  app F := colimitAugmentationApp A Ubullet F
  naturality _ _ t := colimitAugmentation_naturality A Ubullet t

/-- Cosimplicial evaluation of one presheaf, bundled with its canonical augmentation to the
presheaf colimit. -/
@[stacks 08Q9 "augmented cosimplicial evaluation object"]
def augmentedObj (Ubullet : CosimplicialObject C) (F : Cᵒᵖ ⥤ A) :
    SimplicialObject.Augmented A where
  left := (simplicial A Ubullet).obj F
  right := (colim : (Cᵒᵖ ⥤ A) ⥤ A).obj F
  hom := colimitAugmentationApp A Ubullet F

/-- The morphism of augmented cosimplicial evaluations induced by a coefficient morphism. -/
@[stacks 08Q9 "augmented cosimplicial evaluation map"]
def augmentedMap (Ubullet : CosimplicialObject C) {F G : Cᵒᵖ ⥤ A} (t : F ⟶ G) :
    augmentedObj A Ubullet F ⟶ augmentedObj A Ubullet G :=
  CommaMorphism.mk ((simplicial A Ubullet).map t)
    ((colim : (Cᵒᵖ ⥤ A) ⥤ A).map t)
    (colimitAugmentation_naturality A Ubullet t)

/-- The augmented evaluation map attached to an identity is the identity. -/
@[stacks 08Q9 "augmented cosimplicial evaluation identity law"]
theorem augmentedMap_id (Ubullet : CosimplicialObject C) (F : Cᵒᵖ ⥤ A) :
    augmentedMap A Ubullet (𝟙 F) = 𝟙 _ := sorry

/-- Augmented evaluation maps preserve composition. -/
@[stacks 08Q9 "augmented cosimplicial evaluation composition law"]
theorem augmentedMap_comp
    (Ubullet : CosimplicialObject C) {F G H : Cᵒᵖ ⥤ A}
    (f : F ⟶ G) (g : G ⟶ H) :
    augmentedMap A Ubullet (f ≫ g) =
      augmentedMap A Ubullet f ≫ augmentedMap A Ubullet g := sorry

/-- Cosimplicial evaluation with its colimit augmentation, functorial in the coefficient
presheaf. -/
@[stacks 08Q9 "functorial augmented cosimplicial evaluation"]
def augmented (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ A) ⥤ SimplicialObject.Augmented A where
  obj F := augmentedObj A Ubullet F
  map t := augmentedMap A Ubullet t
  map_id F := augmentedMap_id A Ubullet F
  map_comp f g := augmentedMap_comp A Ubullet f g

/-- Forgetting the augmentation recovers cosimplicial evaluation. -/
@[simp, stacks 08Q9 "augmented evaluation underlying simplicial functor"]
theorem augmented_comp_drop (Ubullet : CosimplicialObject C) :
    augmented A Ubullet ⋙ SimplicialObject.Augmented.drop = simplicial A Ubullet := sorry

/-- Taking augmentation points recovers the presheaf colimit functor. -/
@[simp, stacks 08Q9 "augmented evaluation point functor"]
theorem augmented_comp_point (Ubullet : CosimplicialObject C) :
    augmented A Ubullet ⋙ SimplicialObject.Augmented.point =
      (colim : (Cᵒᵖ ⥤ A) ⥤ A) := sorry

/-- The canonical chain-level augmentation from the alternating-face complex of cosimplicial
evaluation to the degree-zero complex on the presheaf colimit. -/
@[stacks 08Q9 "cosimplicial evaluation chain augmentation"]
def chainAugmentation (Ubullet : CosimplicialObject C) :
    augmented A Ubullet ⋙ SimplicialObject.Augmented.drop ⋙
          alternatingFaceMapComplex A ⟶
      augmented A Ubullet ⋙ SimplicialObject.Augmented.point ⋙
          ChainComplex.single₀ A :=
  Functor.whiskerLeft (augmented A Ubullet) AlternatingFaceMapComplex.ε

end ColimitAugmentation

/-- The chain complex obtained by applying the alternating-face construction after evaluation on
a cosimplicial object. -/
@[stacks 08Q9 "cosimplicial evaluation complex"]
abbrev complex (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ A) ⥤ ChainComplex A ℕ :=
  simplicial A Ubullet ⋙ alternatingFaceMapComplex A

variable [HasDerivedCategory A]

/-- The derived-category realization of cosimplicial evaluation. -/
@[stacks 08Q9 "derived cosimplicial evaluation"]
noncomputable abbrev toDerived (Ubullet : CosimplicialObject C) :
    (Cᵒᵖ ⥤ A) ⥤ DerivedCategory A :=
  complex A Ubullet ⋙
    ComplexShape.embeddingDownNat.extendFunctor A ⋙ DerivedCategory.Q

section DerivedAugmentation

variable [HasColimitsOfShape Cᵒᵖ A]

/-- The canonical colimit augmentation after extending the alternating-face complex to integer
degrees and localizing to the derived category. It retains the explicit augmented source and
target presentations; `augmented_comp_drop` and `augmented_comp_point` identify their underlying
functors with cosimplicial evaluation and colimit. -/
@[stacks 08Q9 "derived cosimplicial evaluation augmentation"]
noncomputable def derivedAugmentation (Ubullet : CosimplicialObject C) :
    augmented A Ubullet ⋙ SimplicialObject.Augmented.drop ⋙
          alternatingFaceMapComplex A ⋙ ComplexShape.embeddingDownNat.extendFunctor A ⋙
          DerivedCategory.Q ⟶
      augmented A Ubullet ⋙ SimplicialObject.Augmented.point ⋙
          ChainComplex.single₀ A ⋙ ComplexShape.embeddingDownNat.extendFunctor A ⋙
          DerivedCategory.Q :=
  Functor.whiskerRight (chainAugmentation A Ubullet)
    (ComplexShape.embeddingDownNat.extendFunctor A ⋙ DerivedCategory.Q)

end DerivedAugmentation

end Evaluation

end CosimplicialObject

end CategoryTheory
