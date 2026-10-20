/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.Presentation.Tower
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.ShortComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Presentation morphisms on represented Hom short complexes

A morphism of telescope presentations acts contravariantly on the associated Milnor short
complex. This leaf owns the two defining squares and the component, identity, and composition
API of that action.
@stack 0CQX
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit.RepresentedHom

open SequentialInverseSystem.Milnor.ProductCone

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The first-derived-limit inclusion is contravariantly natural in a morphism of telescope
presentations. -/
@[reassoc, stacks 0CQX]
theorem r1Inclusion_precomp {K L : ℕ ⥤ D} {α : K ⟶ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (φ : Presentation.Hom α P Q) (Z : D) :
    canonicalR1.map (shiftedTowerPrecomp α Z) ≫ r1Inclusion P Z =
      r1Inclusion Q Z ≫ (preadditiveYoneda.obj Z).map φ.hom.op := sorry

/-- The map to the inverse limit is contravariantly natural in a morphism of telescope
presentations. -/
@[reassoc, stacks 0CQX]
theorem homToLimit_precomp {K L : ℕ ⥤ D} {α : K ⟶ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (φ : Presentation.Hom α P Q) (Z : D) :
    (preadditiveYoneda.obj Z).map φ.hom.op ≫ homToLimit P Z =
      homToLimit Q Z ≫ Limits.lim.map (towerPrecomp α Z) := sorry

/-- A morphism of telescope presentations induces a contravariant morphism of represented Hom
Milnor short complexes. -/
@[stacks 0CQX]
def shortComplexPrecomp {K L : ℕ ⥤ D} {α : K ⟶ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (φ : Presentation.Hom α P Q) (Z : D) :
    shortComplex Q Z ⟶ shortComplex P Z where
  τ₁ := canonicalR1.map (shiftedTowerPrecomp α Z)
  τ₂ := (preadditiveYoneda.obj Z).map φ.hom.op
  τ₃ := Limits.lim.map (towerPrecomp α Z)
  comm₁₂ := r1Inclusion_precomp φ Z
  comm₂₃ := homToLimit_precomp φ Z

/-- The left component of presentation precomposition is the induced map on canonical first
derived limits. -/
@[simp]
theorem shortComplexPrecomp_τ₁ {K L : ℕ ⥤ D} {α : K ⟶ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (φ : Presentation.Hom α P Q) (Z : D) :
    (shortComplexPrecomp φ Z).τ₁ =
      canonicalR1.map (shiftedTowerPrecomp α Z) := sorry

/-- The middle component of presentation precomposition is precomposition on represented
Hom. -/
@[simp]
theorem shortComplexPrecomp_τ₂ {K L : ℕ ⥤ D} {α : K ⟶ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (φ : Presentation.Hom α P Q) (Z : D) :
    (shortComplexPrecomp φ Z).τ₂ =
      (preadditiveYoneda.obj Z).map φ.hom.op := sorry

/-- The right component of presentation precomposition is the induced map on inverse
limits. -/
@[simp]
theorem shortComplexPrecomp_τ₃ {K L : ℕ ⥤ D} {α : K ⟶ L} {X Y : D}
    {P : Presentation K X} {Q : Presentation L Y}
    (φ : Presentation.Hom α P Q) (Z : D) :
    (shortComplexPrecomp φ Z).τ₃ = Limits.lim.map (towerPrecomp α Z) := sorry

/-- The identity presentation morphism acts as the identity on represented Hom short
complexes. -/
@[simp]
theorem shortComplexPrecomp_id {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (Z : D) :
    shortComplexPrecomp (Presentation.Hom.id P) Z = 𝟙 (shortComplex P Z) := sorry

/-- Presentation precomposition reverses composition. -/
@[simp]
theorem shortComplexPrecomp_comp
    {K L M : ℕ ⥤ D} {α : K ⟶ L} {β : L ⟶ M} {X Y W : D}
    {P : Presentation K X} {Q : Presentation L Y} {R : Presentation M W}
    (φ : Presentation.Hom α P Q) (ψ : Presentation.Hom β Q R) (Z : D) :
    shortComplexPrecomp (φ.comp ψ) Z =
      shortComplexPrecomp ψ Z ≫ shortComplexPrecomp φ Z := sorry

end CategoryTheory.HomotopyColimit.RepresentedHom

end
