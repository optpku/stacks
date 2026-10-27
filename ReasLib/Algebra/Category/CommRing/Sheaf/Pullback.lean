/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
public import Mathlib.CategoryTheory.Sites.Limits

/-! # Sections of pullbacks of commutative ring sheaves -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf.CommRing

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Objectwise identification of a sheaf-level pullback with the pullback of sections. -/
def pullbackAppIso {A B E : Sheaf J CommRingCat.{w}} (f : A ⟶ E) (g : B ⟶ E) (U : Cᵒᵖ) :
    (Limits.pullback f g).obj.obj U ≅ Limits.pullback (f.hom.app U) (g.hom.app U) :=
  ((CategoryTheory.evaluation (Cᵒᵖ) CommRingCat.{w}).obj U).mapIso
      (preservesLimitIso (sheafToPresheaf J CommRingCat.{w}) (cospan f g) ≪≫
        HasLimit.isoOfNatIso
          (cospanCompIso (sheafToPresheaf J CommRingCat.{w}) f g)) ≪≫
    pullbackObjIso f.hom g.hom U

/-- Pairing of compatible sections into a sheaf-level pullback. -/
def pullbackSectionMk {A B E : Sheaf J CommRingCat.{w}} (f : A ⟶ E) (g : B ⟶ E) (U : Cᵒᵖ)
    (a : A.obj.obj U) (b : B.obj.obj U) (h : f.hom.app U a = g.hom.app U b) :
    (Limits.pullback f g).obj.obj U :=
  (pullbackAppIso f g U).inv.hom
    ((IsLimit.conePointUniqueUpToIso
        (limit.isLimit (cospan (f.hom.app U) (g.hom.app U)))
        (CommRingCat.pullbackConeIsLimit (f.hom.app U) (g.hom.app U))).inv.hom
      ⟨(a, b), h⟩)

/-- The first projection of a paired section is its first coordinate. -/
theorem pullbackSectionMk_fst {A B E : Sheaf J CommRingCat.{w}}
    (f : A ⟶ E) (g : B ⟶ E) (U : Cᵒᵖ)
    (a : A.obj.obj U) (b : B.obj.obj U) (h : f.hom.app U a = g.hom.app U b) :
    (Limits.pullback.fst f g).hom.app U (pullbackSectionMk f g U a b h) = a := sorry

/-- The second projection of a paired section is its second coordinate. -/
theorem pullbackSectionMk_snd {A B E : Sheaf J CommRingCat.{w}}
    (f : A ⟶ E) (g : B ⟶ E) (U : Cᵒᵖ)
    (a : A.obj.obj U) (b : B.obj.obj U) (h : f.hom.app U a = g.hom.app U b) :
    (Limits.pullback.snd f g).hom.app U (pullbackSectionMk f g U a b h) = b := sorry

end CategoryTheory.Sheaf.CommRing
