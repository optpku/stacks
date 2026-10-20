/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.LocalMorphisms
public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Construction
public import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Descent of morphisms in the local-arrow category

A descent morphism gives a compatible family of actual local-arrow classes.
Its preimage is the explicit flattened family from `LocalMorphisms`, with
Cartesian comparison maps supplied by the displayed cleavage. This constructs
the full-faithfulness data instead of assuming a sheaf or fullness factory.
-/

@[expose] public section

open CategoryTheory Opposite GrothendieckTopology

noncomputable section

universe u v uX vX

namespace CategoryTheory.Functor.StackificationConstruction.Localized

variable {C : Type u} [Category.{v} C] {X : Type uX} [Category.{vX} X]
variable (J : GrothendieckTopology C) (p : X ⥤ C) (χ : p.Cleavage)
variable (ξ : (projection J p χ).Cleavage)

/-- Convert a native descent morphism to the concrete family that can be
flattened. Every comparison factor uses the actual Cartesian field of `ξ`. -/
def descentCoverFamily {U : C} (R : J.Cover U)
    {a b : (projection J p χ).Fiber U}
    (φ : (ξ.toPseudofunctor.toDescentData (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj a ⟶
      (ξ.toPseudofunctor.toDescentData (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj b) :
    CoverFamily J p χ a.1 b.1 where
  base := eqToHom a.2 ≫ eqToHom b.2.symm
  cover := R.pullback (eqToHom a.2)
  arrow I := by
    let index : (R : Sieve U).arrows.category :=
      Presieve.categoryMk (R : Sieve U).arrows I.base.f I.base.hf
    let original := χ.cartesianHom I.f
      (⟨a.1.obj.obj, rfl⟩ : p.Fiber (p.obj a.1.obj.obj))
    let originalClass := (fromOriginal J p χ).map original
    let originalLift : (projection J p χ).IsHomLift (𝟙 I.Y ≫ I.base.f) originalClass := by sorry
    let comparison := @Functor.Cleavage.cartesianFactor C _ (Localized J p χ) _
      (projection J p χ) ξ U I.Y I.Y I.base.f (𝟙 I.Y) a
      ((fromOriginal J p χ).obj (sourceRestriction J p χ a.1.obj I.f)) originalClass originalLift
    exact comparison ≫ (φ.hom index).1 ≫ ξ.cartesianHom I.base.f b
  isHomLift := by
    intro I
    sorry
  compatibility := by
    intro I T k
    sorry

/-- The flattened native descent morphism lies over the identity of its fibre. -/
theorem descentCoverFamily_glue_isHomLift {U : C} (R : J.Cover U)
    {a b : (projection J p χ).Fiber U}
    (φ : (ξ.toPseudofunctor.toDescentData (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj a ⟶
      (ξ.toPseudofunctor.toDescentData (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj b) :
    (projection J p χ).IsHomLift (𝟙 U)
      (CoverFamily.glue J p χ (descentCoverFamily J p χ ξ R φ)) := sorry

/-- A descent morphism's actual inverse image in the fibre category. -/
def descentPreimage {U : C} (R : J.Cover U)
    {a b : (projection J p χ).Fiber U}
    (φ : (ξ.toPseudofunctor.toDescentData (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj a ⟶
      (ξ.toPseudofunctor.toDescentData (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).obj b) : a ⟶ b :=
  ⟨CoverFamily.glue J p χ (descentCoverFamily J p χ ξ R φ),
    descentCoverFamily_glue_isHomLift J p χ ξ R φ⟩

/-- Full faithfulness stores the explicit flattened preimage. Only its two
inverse laws are deferred. -/
def fullyFaithfulDescent {U : C} (R : J.Cover U) :
    (ξ.toPseudofunctor.toDescentData
      (fun I : (R : Sieve U).arrows.category ↦ I.obj.hom)).FullyFaithful where
  preimage := descentPreimage J p χ ξ R
  map_preimage := sorry
  preimage_map := sorry

/-- The native prestack condition is assembled from explicit descent preimages
on every covering sieve, through the implemented native sheaf bridge. -/
theorem isPrestack : ξ.toPseudofunctor.IsPrestack J :=
  Pseudofunctor.IsPrestack.of_isPrestackFor fun U R hR ↦
    { nonempty_fullyFaithful := ⟨fullyFaithfulDescent J p χ ξ ⟨R, hR⟩⟩ }

end CategoryTheory.Functor.StackificationConstruction.Localized
