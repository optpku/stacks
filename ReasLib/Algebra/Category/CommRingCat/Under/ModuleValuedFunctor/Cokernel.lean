/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Category

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace ModuleValuedFunctor

variable {A : CommRingCat.{u}}

/-- The pointwise cokernel of a morphism of bundled module-valued functors. -/
def pointwiseCokernel {F G : bundled.{u, v} A} (f : F ⟶ G) :
    bundled.{u, v} A where
  obj B := cokernel (f.app B)
  map {B B'} g :=
    cokernel.desc (f.app B)
      (G.map g ≫ (ModuleCat.restrictScalars g.right.hom).map (cokernel.π (f.app B'))) sorry
  map_id := sorry
  map_comp := sorry

/-- The canonical projection to the pointwise cokernel. -/
def pointwiseCokernelπ {F G : bundled.{u, v} A} (f : F ⟶ G) :
    G ⟶ pointwiseCokernel f where
  app B := cokernel.π (f.app B)
  naturality := sorry

/-- The pointwise cokernel projection annihilates the original morphism. -/
theorem comp_pointwiseCokernelπ {F G : bundled.{u, v} A} (f : F ⟶ G) :
    f ≫ pointwiseCokernelπ f =
      ((bundledHasZeroMorphisms.{u, v} A).zero F (pointwiseCokernel f)).zero := sorry

/-- A morphism annihilating the original map descends through its pointwise cokernel. -/
def pointwiseCokernelDesc {F G H : bundled.{u, v} A} (f : F ⟶ G)
    (g : G ⟶ H)
    (h : f ≫ g = ((bundledHasZeroMorphisms.{u, v} A).zero F H).zero) :
    pointwiseCokernel f ⟶ H where
  app B := cokernel.desc (f.app B) (g.app B) sorry
  naturality := sorry

/-- The canonical cofork exhibiting the pointwise cokernel. -/
def pointwiseCokernelCofork {F G : bundled.{u, v} A} (f : F ⟶ G) :
    Cofork f ((bundledHasZeroMorphisms.{u, v} A).zero F G).zero :=
  Cofork.ofπ (pointwiseCokernelπ f) (by
    rw [comp_pointwiseCokernelπ]
    exact ((bundledHasZeroMorphisms.{u, v} A).zero_comp F (pointwiseCokernelπ f)).symm)

/-- The pointwise cokernel cofork satisfies the categorical universal property. -/
def pointwiseCokernelCoforkIsColimit {F G : bundled.{u, v} A} (f : F ⟶ G) :
    IsColimit (pointwiseCokernelCofork f) where
  desc s := pointwiseCokernelDesc f (Cofork.π s) (by
    exact (Cofork.condition s).trans
      ((bundledHasZeroMorphisms.{u, v} A).zero_comp F (Cofork.π s)))
  fac := sorry
  uniq := sorry

end ModuleValuedFunctor
