/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.Sheaves.Limits

/-! # Sections of pullbacks of commutative-ring sheaves -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf.CommRing

variable {Y : TopCat.{u}}

/-- Objectwise identification of a sheaf-level pullback with the pullback of sections. -/
def pullbackAppIso {A B E : TopCat.Sheaf CommRingCat.{u} Y} (π : A ⟶ E) (ρ : B ⟶ E)
    (U : (Opens Y)ᵒᵖ) :
    (Limits.pullback π ρ).obj.obj U ≅ Limits.pullback (π.hom.app U) (ρ.hom.app U) :=
  ((CategoryTheory.evaluation ((Opens Y)ᵒᵖ) CommRingCat.{u}).obj U).mapIso
      (preservesLimitIso (sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
        (cospan π ρ) ≪≫
        HasLimit.isoOfNatIso
          (cospanCompIso (sheafToPresheaf (Opens.grothendieckTopology Y) CommRingCat.{u})
            π ρ)) ≪≫
    pullbackObjIso π.hom ρ.hom U

/-- Pairing of compatible sections into a sheaf-level pullback. -/
def pullbackSectionMk {A B E : TopCat.Sheaf CommRingCat.{u} Y} (π : A ⟶ E) (ρ : B ⟶ E)
    (U : (Opens Y)ᵒᵖ)
    (a : A.obj.obj U) (b : B.obj.obj U) (h : π.hom.app U a = ρ.hom.app U b) :
    (Limits.pullback π ρ).obj.obj U :=
  (pullbackAppIso π ρ U).inv.hom
    ((IsLimit.conePointUniqueUpToIso
        (limit.isLimit (cospan (π.hom.app U) (ρ.hom.app U)))
        (CommRingCat.pullbackConeIsLimit (π.hom.app U) (ρ.hom.app U))).inv.hom
      ⟨(a, b), h⟩)

/-- The fst projection of the section formed from a compatible pair is its corresponding component. -/
theorem pullbackSectionMk_fst
    {A B E : TopCat.Sheaf CommRingCat.{u} Y} (π : A ⟶ E) (ρ : B ⟶ E)
    (U : (Opens Y)ᵒᵖ) (a : A.obj.obj U) (b : B.obj.obj U)
    (h : π.hom.app U a = ρ.hom.app U b) :
    (Limits.pullback.fst π ρ).hom.app U (pullbackSectionMk π ρ U a b h) = a := sorry

/-- The snd projection of the section formed from a compatible pair is its corresponding component. -/
theorem pullbackSectionMk_snd
    {A B E : TopCat.Sheaf CommRingCat.{u} Y} (π : A ⟶ E) (ρ : B ⟶ E)
    (U : (Opens Y)ᵒᵖ) (a : A.obj.obj U) (b : B.obj.obj U)
    (h : π.hom.app U a = ρ.hom.app U b) :
    (Limits.pullback.snd π ρ).hom.app U (pullbackSectionMk π ρ U a b h) = b := sorry

end TopCat.Sheaf.CommRing
