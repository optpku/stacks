/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Slice.Restrict
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Factorization
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial restriction along a discrete fibration

Restriction along `G : B ⥤ C` is functorial on strict-slice morphisms and
`2`-morphisms whenever `G` is a discrete fibration. Its public intermediate
based maps isolate the locally induced bicategory representation from
downstream consumers.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe uB uC vB vC

namespace CategoryTheory.FiberedCategoryOver.Slice.Restrict

open Bicategory
open scoped CategoryTheory.Bicategory

variable {B : Type uB} {C : Type uC}
variable [Category.{vB} B] [Category.{vC} C]
variable {G : B ⥤ C} [G.IsDiscreteFibration]

namespace basedMap

/-- The ambient total functor of a strict-slice morphism commutes with its
restricted projections to `B`. -/
theorem toFunctor_comm
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    (F : X ⟶ Y) :
    FiberedCategoryOver.toFunctor (StrictSlice.Hom.hom F) ⋙ (obj Y).p =
      (obj X).p := sorry

/-- The ambient based morphism and the two structural morphisms form the
strict factorization represented by a strict-slice triangle. -/
theorem comm
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    (F : X ⟶ Y) :
    BasedFunctor.comp
        (FiberedCategoryOver.toBasedFunctor (StrictSlice.Hom.hom F))
        (FiberedCategoryOver.toBasedFunctor Y.hom) =
      FiberedCategoryOver.toBasedFunctor X.hom := sorry

end basedMap

/-- The based functor over `B` underlying restriction of a strict-slice
morphism. -/
def basedMap
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    (F : X ⟶ Y) :
    (obj X).toBasedCategory ⥤ᵇ (obj Y).toBasedCategory :=
  BasedFunctor.Factorization.overTarget
    (FiberedCategoryOver.toBasedFunctor (StrictSlice.Hom.hom F))
    (basedMap.comm F)

namespace basedMap

/-- Restriction of a strict-slice morphism preserves strongly cartesian
morphisms over `B`. -/
theorem preservesStronglyCartesian
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    (F : X ⟶ Y) :
    (basedMap F).PreservesStronglyCartesian := sorry

/-- The total functor of the restricted based map is the ambient total functor
of the strict-slice morphism. -/
@[simp]
theorem toFunctor
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    (F : X ⟶ Y) :
    (basedMap F).toFunctor =
      FiberedCategoryOver.toFunctor (StrictSlice.Hom.hom F) := sorry

end basedMap

/-- Restriction on `1`-morphisms of the strict slice over `G`. -/
def map
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    (F : X ⟶ Y) : obj X ⟶ obj Y :=
  FiberedCategoryOver.ofBasedFunctor
    (basedMap F) (basedMap.preservesStronglyCartesian F)

namespace map

/-- The total functor underlying restriction on a morphism is its ambient total
functor. -/
@[simp]
theorem toFunctor
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    (F : X ⟶ Y) :
    FiberedCategoryOver.toFunctor (map F) =
      FiberedCategoryOver.toFunctor (StrictSlice.Hom.hom F) := sorry

end map

namespace basedMap₂

/-- The ambient natural transformation of a strict-slice `2`-morphism is over
the identity for the restricted based maps. -/
theorem overId
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    {F H : X ⟶ Y} (eta : F ⟶ H) :
    eqToHom (basedMap F).w.symm ≫
        Functor.whiskerRight
          (FiberedCategoryOver.toNatTrans (StrictSlice.Hom₂.hom eta))
          (obj Y).p ≫
          eqToHom (basedMap H).w =
      𝟙 (obj X).p := sorry

end basedMap₂

/-- The based natural transformation over `B` underlying restriction of a
strict-slice `2`-morphism. -/
def basedMap₂
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    {F H : X ⟶ Y} (eta : F ⟶ H) :
    basedMap F ⟶ basedMap H :=
  BasedNatTrans.ofOverId
    (FiberedCategoryOver.toNatTrans (StrictSlice.Hom₂.hom eta))
    (basedMap₂.overId eta)

namespace basedMap₂

/-- The total natural transformation of a restricted based `2`-morphism is
the ambient total natural transformation of the strict-slice cell. -/
@[simp]
theorem toNatTrans
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    {F H : X ⟶ Y} (eta : F ⟶ H) :
    (basedMap₂ eta).toNatTrans =
      FiberedCategoryOver.toNatTrans (StrictSlice.Hom₂.hom eta) := sorry

end basedMap₂

/-- Restriction on `2`-morphisms of the strict slice over `G`. -/
def map₂
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    {F H : X ⟶ Y} (eta : F ⟶ H) : map F ⟶ map H :=
  FiberedCategoryOver.ofBasedNatTrans (basedMap₂ eta)

namespace map₂

/-- The total natural transformation underlying restriction on a `2`-morphism
is its ambient total natural transformation. -/
@[simp]
theorem toNatTrans
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    {F H : X ⟶ Y} (eta : F ⟶ H) :
    FiberedCategoryOver.toNatTrans (map₂ eta) =
      FiberedCategoryOver.toNatTrans (StrictSlice.Hom₂.hom eta) := sorry

end map₂

/-- Two restriction `2`-morphisms agree when all of their total-category
components agree. -/
theorem map₂.ext
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    {F H : X ⟶ Y} {eta theta : F ⟶ H}
    (h : ∀ x : (obj X).total,
      (FiberedCategoryOver.toNatTrans (map₂ eta)).app x =
        (FiberedCategoryOver.toNatTrans (map₂ theta)).app x) :
    map₂ eta = map₂ theta := sorry

/-- Restriction sends identity morphisms to identity morphisms. -/
@[simp]
theorem map.id
    (X : StrictSlice (FiberedCategoryOver.ofFunctor G)) :
    map (𝟙 X) = 𝟙 (obj X) := sorry

/-- Restriction sends composites to composites. -/
@[simp]
theorem map.comp
    {X Y Z : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    (F : X ⟶ Y) (H : Y ⟶ Z) :
    map (F ≫ H) = map F ≫ map H := sorry

/-- Restriction sends identity `2`-morphisms to identity `2`-morphisms. -/
@[simp]
theorem map₂.id
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    (F : X ⟶ Y) : map₂ (𝟙 F) = 𝟙 (map F) := sorry

/-- Restriction preserves vertical composition of `2`-morphisms. -/
@[simp]
theorem map₂.comp
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    {F H K : X ⟶ Y} (eta : F ⟶ H) (theta : H ⟶ K) :
    map₂ (eta ≫ theta) = map₂ eta ≫ map₂ theta := sorry

/-- Restriction preserves left whiskering with the transports determined by its
strict composition law. -/
theorem map₂.whiskerLeft
    {X Y Z : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    (F : X ⟶ Y) {H K : Y ⟶ Z} (eta : H ⟶ K) :
    map₂ (F ◁ eta) =
      eqToHom (map.comp F H) ≫ map F ◁ map₂ eta ≫
        eqToHom (map.comp F K).symm := sorry

/-- Restriction preserves right whiskering with the transports determined by
its strict composition law. -/
theorem map₂.whiskerRight
    {X Y Z : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    {F H : X ⟶ Y} (eta : F ⟶ H) (K : Y ⟶ Z) :
    map₂ (eta ▷ K) =
      eqToHom (map.comp F K) ≫ map₂ eta ▷ map K ≫
        eqToHom (map.comp H K).symm := sorry

/-- The strict-pseudofunctor core of restriction along `G`. -/
private def core :
    StrictPseudofunctorPreCore
      (StrictSlice (FiberedCategoryOver.ofFunctor G))
      (FiberedCategoryOver.{uB, vB, uB, vB} B) where
  obj := obj
  map := map
  map₂ := map₂
  map_id := map.id
  map_comp := map.comp
  map₂_id := map₂.id
  map₂_comp := map₂.comp
  map₂_whisker_left := map₂.whiskerLeft
  map₂_whisker_right := map₂.whiskerRight

/-- Restriction from the strict slice over a discrete fibration `G` to fibred
categories over its domain `B`. -/
def functor (G : B ⥤ C) [G.IsDiscreteFibration] :
    StrictPseudofunctor
      (StrictSlice (FiberedCategoryOver.ofFunctor G))
      (FiberedCategoryOver.{uB, vB, uB, vB} B) :=
  StrictPseudofunctor.mk'' (core (G := G))

namespace functor

/-- The restriction strict pseudofunctor acts on objects by `Restrict.obj`. -/
@[simp]
theorem obj
    (G : B ⥤ C) [G.IsDiscreteFibration]
    (X : StrictSlice (FiberedCategoryOver.ofFunctor G)) :
    (functor G).obj X = Restrict.obj X := sorry

/-- The restriction strict pseudofunctor acts on morphisms by `Restrict.map`. -/
@[simp]
theorem map
    (G : B ⥤ C) [G.IsDiscreteFibration]
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    (F : X ⟶ Y) : (functor G).map F = Restrict.map F := sorry

/-- The restriction strict pseudofunctor acts on `2`-morphisms by
`Restrict.map₂`. -/
@[simp]
theorem map₂
    (G : B ⥤ C) [G.IsDiscreteFibration]
    {X Y : StrictSlice (FiberedCategoryOver.ofFunctor G)}
    {F H : X ⟶ Y} (eta : F ⟶ H) :
    (functor G).map₂ eta = Restrict.map₂ eta := sorry

end functor

/- The non-`Prop` payload below is inherited from the supplied strict-slice
morphisms and cells. Any `sorryAx` is confined to compatibility and coherence
proofs. -/

end CategoryTheory.FiberedCategoryOver.Slice.Restrict
