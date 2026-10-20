/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.ShortComplex
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.Tower.Additive
public import ReasLib.CategoryTheory.Preadditive.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of the represented Hom Milnor short complex

@stack 0CQX

The represented Hom short complex is functorial in its target. This leaf imports the additive
tower API and owns the naturality squares, induced short-complex morphism, and resulting additive
functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit.RepresentedHom

open SequentialInverseSystem.Milnor.ProductCone

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The shifted-product map is natural in the represented target. -/
@[reassoc]
theorem shiftedProductToHom_naturality {K : ℕ ⥤ D} {X L M : D}
    (P : Presentation K X) (f : L ⟶ M) :
    SequentialInverseSystem.productMap (shiftedTowerMap K f) ≫ shiftedProductToHom P M =
      shiftedProductToHom P L ≫ (preadditiveYoneda.map f).app (op X) := sorry

/-- The first-derived-limit inclusion is natural in the represented target. -/
@[reassoc]
theorem r1Inclusion_naturality {K : ℕ ⥤ D} {X L M : D}
    (P : Presentation K X) (f : L ⟶ M) :
    canonicalR1.map (shiftedTowerMap K f) ≫ r1Inclusion P M =
      r1Inclusion P L ≫ (preadditiveYoneda.map f).app (op X) := sorry

/-- The map from represented Hom to the inverse limit is natural in the represented target. -/
@[reassoc]
theorem homToLimit_naturality {K : ℕ ⥤ D} {X L M : D}
    (P : Presentation K X) (f : L ⟶ M) :
    (preadditiveYoneda.map f).app (op X) ≫ homToLimit P M =
      homToLimit P L ≫ Limits.lim.map (towerMap K f) := sorry

/-- Postcomposition with a target morphism gives a morphism between represented Hom short
complexes. -/
@[stacks 0CQX]
def shortComplexMap {K : ℕ ⥤ D} {X L M : D} (P : Presentation K X) (f : L ⟶ M) :
    shortComplex P L ⟶ shortComplex P M where
  τ₁ := canonicalR1.map (shiftedTowerMap K f)
  τ₂ := (preadditiveYoneda.map f).app (op X)
  τ₃ := Limits.lim.map (towerMap K f)
  comm₁₂ := r1Inclusion_naturality P f
  comm₂₃ := homToLimit_naturality P f

/-- The left component of `shortComplexMap` is the canonical map on first derived limits. -/
@[simp]
theorem shortComplexMap_τ₁ {K : ℕ ⥤ D} {X L M : D} (P : Presentation K X)
    (f : L ⟶ M) :
    (shortComplexMap P f).τ₁ = canonicalR1.map (shiftedTowerMap K f) := sorry

/-- The middle component of `shortComplexMap` is postcomposition on represented Hom. -/
@[simp]
theorem shortComplexMap_τ₂ {K : ℕ ⥤ D} {X L M : D} (P : Presentation K X)
    (f : L ⟶ M) :
    (shortComplexMap P f).τ₂ = (preadditiveYoneda.map f).app (op X) := sorry

/-- The right component of `shortComplexMap` is the induced map on inverse limits. -/
@[simp]
theorem shortComplexMap_τ₃ {K : ℕ ⥤ D} {X L M : D} (P : Presentation K X)
    (f : L ⟶ M) :
    (shortComplexMap P f).τ₃ = Limits.lim.map (towerMap K f) := sorry

/-- The represented Hom short-complex map associated to an identity is the identity. -/
@[simp]
theorem shortComplexMap_id {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D) :
    shortComplexMap P (𝟙 L) = 𝟙 (shortComplex P L) := sorry

/-- Represented Hom short-complex maps preserve composition. -/
@[simp]
theorem shortComplexMap_comp {K : ℕ ⥤ D} {X L M N : D} (P : Presentation K X)
    (f : L ⟶ M) (g : M ⟶ N) :
    shortComplexMap P (f ≫ g) = shortComplexMap P f ≫ shortComplexMap P g := sorry

/-- Represented Hom short-complex maps preserve addition in the target morphism. -/
@[simp, stacks 0CQX]
theorem shortComplexMap_add {K : ℕ ⥤ D} {X L M : D} (P : Presentation K X)
    (f g : L ⟶ M) :
    shortComplexMap P (f + g) = shortComplexMap P f + shortComplexMap P g := sorry

/-- The represented Hom Milnor short complex as a functor of the represented target. -/
@[stacks 0CQX]
def functor {K : ℕ ⥤ D} {X : D} (P : Presentation K X) :
    D ⥤ ShortComplex AddCommGrpCat where
  obj L := shortComplex P L
  map f := shortComplexMap P f
  map_id L := shortComplexMap_id P L
  map_comp f g := shortComplexMap_comp P f g

/-- The represented Hom short-complex functor evaluates to `shortComplex P L`. -/
@[simp]
theorem functor_obj {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D) :
    (functor P).obj L = shortComplex P L := sorry

/-- The represented Hom short-complex functor maps a morphism by `shortComplexMap`. -/
@[simp]
theorem functor_map {K : ℕ ⥤ D} {X L M : D} (P : Presentation K X) (f : L ⟶ M) :
    (functor P).map f = shortComplexMap P f := sorry

/-- The represented Hom Milnor short-complex functor is additive in its target. -/
@[stacks 0CQX]
instance functorAdditive {K : ℕ ⥤ D} {X : D} (P : Presentation K X) :
    (functor P).Additive := sorry

end CategoryTheory.HomotopyColimit.RepresentedHom

end
