/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Concrete

/-!
# Range factorizations in the category of rings

This file gives the canonical functorial factorization of a ring homomorphism through its range.
It is a neutral dependency for sheaf, module, and other categorical applications.
-/

@[expose] public section

open CategoryTheory

universe u

namespace RingCat

/-- The range of the homomorphism represented by an arrow in `RingCat`. -/
def rangeObject (f : Arrow RingCat.{u}) : RingCat.{u} :=
  RingCat.of f.hom.hom.range

/-- The right-hand map of a morphism of ring arrows sends the source range into the target
range. -/
theorem rangeMap_mem {f g : Arrow RingCat.{u}} (φ : f ⟶ g)
    (y : f.hom.hom.range) : φ.right y.1 ∈ g.hom.hom.range := sorry

/-- The map between ranges induced by a morphism of ring arrows. -/
def rangeMap {f g : Arrow RingCat.{u}} (φ : f ⟶ g) : rangeObject f ⟶ rangeObject g :=
  RingCat.ofHom <|
    (φ.right.hom.comp (Subring.subtype _)).codRestrict _ (rangeMap_mem φ)

/-- The range map of an identity morphism of ring arrows is the identity. -/
theorem rangeMap_id (f : Arrow RingCat.{u}) :
    rangeMap (𝟙 f) = 𝟙 (rangeObject f) := sorry

/-- Range maps preserve composition of morphisms of ring arrows. -/
theorem rangeMap_comp {f g h : Arrow RingCat.{u}} (φ : f ⟶ g) (ψ : g ⟶ h) :
    rangeMap (φ ≫ ψ) = rangeMap φ ≫ rangeMap ψ := sorry

/-- The functor sending a ring homomorphism to its range. -/
def rangeFunctor : Arrow RingCat.{u} ⥤ RingCat.{u} where
  obj := rangeObject
  map := rangeMap
  map_id := rangeMap_id
  map_comp := rangeMap_comp

/-- The surjective range restriction from the source of a ring arrow to its range. -/
def rangeRestriction (f : Arrow RingCat.{u}) : f.left ⟶ rangeObject f :=
  RingCat.ofHom f.hom.hom.rangeRestrict

/-- Range restriction is natural in a ring arrow. -/
theorem rangeRestriction_naturality {f g : Arrow RingCat.{u}} (φ : f ⟶ g) :
    Arrow.leftFunc.map φ ≫ rangeRestriction g =
      rangeRestriction f ≫ rangeFunctor.map φ := sorry

/-- The natural transformation from the source of a ring arrow to its range. -/
def rangeRestrictionNatTrans : Arrow.leftFunc (C := RingCat.{u}) ⟶ rangeFunctor where
  app := rangeRestriction
  naturality := fun _ _ φ ↦ rangeRestriction_naturality φ

/-- The injective inclusion from the range of a ring arrow into its target. -/
def rangeInclusion (f : Arrow RingCat.{u}) : rangeObject f ⟶ f.right :=
  RingCat.ofHom (Subring.subtype f.hom.hom.range)

/-- Range inclusion is natural in a ring arrow. -/
theorem rangeInclusion_naturality {f g : Arrow RingCat.{u}} (φ : f ⟶ g) :
    rangeFunctor.map φ ≫ rangeInclusion g =
      rangeInclusion f ≫ Arrow.rightFunc.map φ := sorry

/-- The natural transformation from the range of a ring arrow to its target. -/
def rangeInclusionNatTrans : rangeFunctor ⟶ Arrow.rightFunc (C := RingCat.{u}) where
  app := rangeInclusion
  naturality := fun _ _ φ ↦ rangeInclusion_naturality φ

/-- Range restriction followed by range inclusion recovers the original ring arrow. -/
theorem rangeRestriction_comp_inclusion :
    rangeRestrictionNatTrans ≫ rangeInclusionNatTrans =
      Arrow.leftToRight (C := RingCat.{u}) := sorry

/-- The range restriction of every ring arrow is surjective. -/
theorem rangeRestriction_surjective (f : Arrow RingCat.{u}) :
    (MorphismProperty.surjective RingCat.{u}) (rangeRestrictionNatTrans.app f) := sorry

/-- The range inclusion of every ring arrow is injective. -/
theorem rangeInclusion_injective (f : Arrow RingCat.{u}) :
    (MorphismProperty.injective RingCat.{u}) (rangeInclusionNatTrans.app f) := sorry

/-- The functorial factorization of a ring homomorphism through its range, with a surjective
range restriction followed by the injective range inclusion. -/
def rangeFactorizationData :
    ConcreteCategory.FunctorialSurjectiveInjectiveFactorizationData RingCat.{u} where
  Z := rangeFunctor
  i := rangeRestrictionNatTrans
  p := rangeInclusionNatTrans
  fac := rangeRestriction_comp_inclusion
  hi := rangeRestriction_surjective
  hp := rangeInclusion_injective

/-- Ring homomorphisms admit a canonical functorial factorization as a surjective map followed
by an injective map. -/
instance instRangeFactorization :
    ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization RingCat.{u} where
  nonempty_functorialFactorizationData := ⟨rangeFactorizationData⟩

end RingCat
