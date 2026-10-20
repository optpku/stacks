/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Endofunctor.MonadResolution.Realization
public import ReasLib.AlgebraicTopology.SimplexCategory.HomCode
public import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Generator presentations of monad resolutions

Typed simplex generator words evaluate to maps between positive endofunctor iterates. The three
degree-zero relations bundle raw unit and multiplication data into a Mathlib `Monad` and construct
the corresponding source-facing cosimplicial resolution.
-/

@[expose] public section

open CategoryTheory.CosimplicialObject
open CategoryTheory.Functor
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace EndofunctorResolution

namespace cosimplicial

/-- Rewrite a simplex morphism between its canonical skeletal representatives. -/
@[stacks 0G5N "canonical covariant simplex morphism representative"]
def canonicalHom {Δ Δ' : SimplexCategory} (θ : Δ ⟶ Δ') :
    SimplexCategory.mk Δ.len ⟶ SimplexCategory.mk Δ'.len :=
  eqToHom (SimplexCategory.mk_len Δ) ≫ θ ≫
    eqToHom (SimplexCategory.mk_len Δ').symm

/-- Evaluate a simplex generator code by inserting the specified unit-like and
multiplication-like transformations. -/
@[stacks 0G5N "cosimplicial generator-code evaluation"]
def evalCode {Y : C ⥤ C} (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y) :
    {m n : ℕ} → SimplexCategory.HomCode m n → (Y ⁺⦋m⦌ ⟶ Y ⁺⦋n⦌)
  | _, _, .id _ => 𝟙 _
  | _, _, .face i code => evalCode d s code ≫ IteratedEndofunctor.coface d _ i
  | _, _, .degeneracy i code =>
      IteratedEndofunctor.codegeneracy s _ i ≫ evalCode d s code

/-- Generator words representing the same simplex morphism have the same evaluation whenever
the unit-like and multiplication-like maps satisfy the monad identities. -/
@[stacks 0G5N "cosimplicial generator-code evaluation independence"]
theorem evalCode.eq_of_toHom_eq {Y : C ⥤ C}
    (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y)
    (hδσ₀ : IteratedEndofunctor.coface d 0 0 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hδσ₁ : IteratedEndofunctor.coface d 0 1 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.codegeneracy s 1 0 ≫
        IteratedEndofunctor.codegeneracy s 0 0 =
      IteratedEndofunctor.codegeneracy s 1 1 ≫
        IteratedEndofunctor.codegeneracy s 0 0)
    {m n : ℕ} (a b : SimplexCategory.HomCode m n)
    (h : a.toHom = b.toHom) :
    evalCode d s a = evalCode d s b := sorry

/-- The computational action of the iterated-endofunctor cosimplicial resolution on a simplex
morphism. -/
@[stacks 0G5N "iterated-endofunctor cosimplicial resolution map"]
noncomputable def map {Y : C ⥤ C}
    (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y) {Δ Δ' : SimplexCategory} (θ : Δ ⟶ Δ') :
    Y ⁺⦋Δ.len⦌ ⟶ Y ⁺⦋Δ'.len⦌ :=
  evalCode d s
    (SimplexCategory.HomCode.ofHom Δ.len Δ'.len (canonicalHom θ))

/-- The canonical cosimplicial resolution map may be computed from any generator word
representing its skeletal simplex morphism. -/
@[stacks 0G5N "cosimplicial resolution map from any generator code"]
theorem map.eq_evalCode {Y : C ⥤ C}
    (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y)
    (hδσ₀ : IteratedEndofunctor.coface d 0 0 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hδσ₁ : IteratedEndofunctor.coface d 0 1 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.codegeneracy s 1 0 ≫
        IteratedEndofunctor.codegeneracy s 0 0 =
      IteratedEndofunctor.codegeneracy s 1 1 ≫
        IteratedEndofunctor.codegeneracy s 0 0)
    {Δ Δ' : SimplexCategory} (θ : Δ ⟶ Δ')
    (code : SimplexCategory.HomCode Δ.len Δ'.len)
    (hcode : code.toHom = canonicalHom θ) :
    map d s θ = evalCode d s code := sorry

/-- The canonical cosimplicial resolution map preserves identities. -/
@[stacks 0G5N "cosimplicial resolution map preserves identities"]
theorem map.id {Y : C ⥤ C}
    (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y)
    (hδσ₀ : IteratedEndofunctor.coface d 0 0 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hδσ₁ : IteratedEndofunctor.coface d 0 1 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.codegeneracy s 1 0 ≫
        IteratedEndofunctor.codegeneracy s 0 0 =
      IteratedEndofunctor.codegeneracy s 1 1 ≫
        IteratedEndofunctor.codegeneracy s 0 0)
    (Δ : SimplexCategory) :
    map d s (𝟙 Δ) = 𝟙 _ := sorry

/-- The canonical cosimplicial resolution map preserves composition. -/
@[stacks 0G5N "cosimplicial resolution map preserves composition"]
theorem map.comp {Y : C ⥤ C}
    (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y)
    (hδσ₀ : IteratedEndofunctor.coface d 0 0 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hδσ₁ : IteratedEndofunctor.coface d 0 1 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.codegeneracy s 1 0 ≫
        IteratedEndofunctor.codegeneracy s 0 0 =
      IteratedEndofunctor.codegeneracy s 1 1 ≫
        IteratedEndofunctor.codegeneracy s 0 0)
    {Δ₀ Δ₁ Δ₂ : SimplexCategory} (θ₁ : Δ₀ ⟶ Δ₁) (θ₂ : Δ₁ ⟶ Δ₂) :
    map d s (θ₁ ≫ θ₂) = map d s θ₁ ≫ map d s θ₂ := sorry

/-- The explicit cosimplicial object generated by unit-like and multiplication-like maps
satisfying the two unit laws and associativity. -/
@[stacks 0G5N "iterated-endofunctor cosimplicial resolution"]
noncomputable def resolution {Y : C ⥤ C}
    (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y)
    (hδσ₀ : IteratedEndofunctor.coface d 0 0 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hδσ₁ : IteratedEndofunctor.coface d 0 1 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.codegeneracy s 1 0 ≫
        IteratedEndofunctor.codegeneracy s 0 0 =
      IteratedEndofunctor.codegeneracy s 1 1 ≫
        IteratedEndofunctor.codegeneracy s 0 0) :
    CosimplicialObject (C ⥤ C) where
  obj Δ := Y ⁺⦋Δ.len⦌
  map θ := map d s θ
  map_id := map.id d s hδσ₀ hδσ₁ hσσ
  map_comp := map.comp d s hδσ₀ hδσ₁ hσσ

/-- The object field of the explicit cosimplicial resolution is the corresponding positive
iterate. -/
@[simp, stacks 0G5N "raw cosimplicial resolution object formula"]
theorem resolution.obj {Y : C ⥤ C}
    (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y)
    (hδσ₀ : IteratedEndofunctor.coface d 0 0 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hδσ₁ : IteratedEndofunctor.coface d 0 1 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.codegeneracy s 1 0 ≫
        IteratedEndofunctor.codegeneracy s 0 0 =
      IteratedEndofunctor.codegeneracy s 1 1 ≫
        IteratedEndofunctor.codegeneracy s 0 0)
    (Δ : SimplexCategory) :
    (resolution d s hδσ₀ hδσ₁ hσσ).obj Δ = Y ⁺⦋Δ.len⦌ := sorry

/-- The map field of the explicit cosimplicial resolution is generator-code evaluation. -/
@[simp, stacks 0G5N "raw cosimplicial resolution map formula"]
theorem resolution.map {Y : C ⥤ C}
    (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y)
    (hδσ₀ : IteratedEndofunctor.coface d 0 0 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hδσ₁ : IteratedEndofunctor.coface d 0 1 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.codegeneracy s 1 0 ≫
        IteratedEndofunctor.codegeneracy s 0 0 =
      IteratedEndofunctor.codegeneracy s 1 1 ≫
        IteratedEndofunctor.codegeneracy s 0 0)
    {Δ Δ' : SimplexCategory} (θ : Δ ⟶ Δ') :
    (resolution d s hδσ₀ hδσ₁ hσσ).map θ = map d s θ := sorry

end cosimplicial

/-- A cosimplicial realization evaluates every simplex morphism by canonical generator-code
evaluation after transport along its degree identifications. -/
@[stacks 0G5N "cosimplicial realization map formula"]
theorem CosimplicialRealization.map.eq {Y : C ⥤ C} {d : 𝟭 C ⟶ Y} {s : Y ⋙ Y ⟶ Y}
    {U : CosimplicialObject (C ⥤ C)} (hU : CosimplicialRealization d s U)
    {Δ Δ' : SimplexCategory} (θ : Δ ⟶ Δ') :
    (hU.objIso Δ.len).hom ≫ cosimplicial.map d s θ =
      U.map θ ≫ (hU.objIso Δ'.len).hom := sorry

/-- The explicit cosimplicial resolution realizes its positive-iterate formulas. -/
@[stacks 0G5N "explicit cosimplicial resolution realization"]
theorem cosimplicial.resolution.realization {Y : C ⥤ C}
    (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y)
    (hδσ₀ : IteratedEndofunctor.coface d 0 0 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hδσ₁ : IteratedEndofunctor.coface d 0 1 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.codegeneracy s 1 0 ≫
        IteratedEndofunctor.codegeneracy s 0 0 =
      IteratedEndofunctor.codegeneracy s 1 1 ≫
        IteratedEndofunctor.codegeneracy s 0 0) :
    CosimplicialRealization d s (cosimplicial.resolution d s hδσ₀ hδσ₁ hσσ) := sorry

/-- The objectwise associativity law extracted from multiplication generator identities. -/
@[stacks 0G5N "generator associativity in components"]
theorem generators.assoc.app {Y : C ⥤ C} (s : Y ⋙ Y ⟶ Y)
    (hσσ : IteratedEndofunctor.codegeneracy s 1 0 ≫
        IteratedEndofunctor.codegeneracy s 0 0 =
      IteratedEndofunctor.codegeneracy s 1 1 ≫
        IteratedEndofunctor.codegeneracy s 0 0) (X : C) :
    Y.map (s.app X) ≫ s.app X = s.app (Y.obj X) ≫ s.app X := sorry

/-- The objectwise left unit law extracted from the first unit generator identity. -/
@[stacks 0G5N "generator left unit in components"]
theorem generators.left_unit.app {Y : C ⥤ C} (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y)
    (hδσ₀ : IteratedEndofunctor.coface d 0 0 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y) (X : C) :
    d.app (Y.obj X) ≫ s.app X = 𝟙 (Y.obj X) := sorry

/-- The objectwise right unit law extracted from the second unit generator identity. -/
@[stacks 0G5N "generator right unit in components"]
theorem generators.right_unit.app {Y : C ⥤ C} (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y)
    (hδσ₁ : IteratedEndofunctor.coface d 0 1 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y) (X : C) :
    Y.map (d.app X) ≫ s.app X = 𝟙 (Y.obj X) := sorry

/-- Turn raw unit and multiplication generators into the canonical Mathlib `Monad` owner. -/
@[stacks 0G5N "monad from iterated-endofunctor generators"]
def toMonad {Y : C ⥤ C} (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y)
    (hδσ₀ : IteratedEndofunctor.coface d 0 0 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hδσ₁ : IteratedEndofunctor.coface d 0 1 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.codegeneracy s 1 0 ≫
        IteratedEndofunctor.codegeneracy s 0 0 =
      IteratedEndofunctor.codegeneracy s 1 1 ≫
        IteratedEndofunctor.codegeneracy s 0 0) : Monad C where
  toFunctor := Y
  η := d
  μ := s
  assoc := generators.assoc.app s hσσ
  left_unit := generators.left_unit.app d s hδσ₀
  right_unit := generators.right_unit.app d s hδσ₁

namespace toMonad

variable {Y : C ⥤ C} (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y)
variable
  (hδσ₀ : IteratedEndofunctor.coface d 0 0 ≫
    IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
  (hδσ₁ : IteratedEndofunctor.coface d 0 1 ≫
    IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
  (hσσ : IteratedEndofunctor.codegeneracy s 1 0 ≫
      IteratedEndofunctor.codegeneracy s 0 0 =
    IteratedEndofunctor.codegeneracy s 1 1 ≫
      IteratedEndofunctor.codegeneracy s 0 0)

/-- The endofunctor underlying the monad constructed from resolution generators. -/
@[simp, stacks 0G5N "underlying endofunctor of the generated monad"]
theorem coe :
    (EndofunctorResolution.toMonad d s hδσ₀ hδσ₁ hσσ : C ⥤ C) = Y := sorry

/-- The unit of the monad constructed from resolution generators. -/
@[simp, stacks 0G5N "unit of the generated monad"]
theorem η : (EndofunctorResolution.toMonad d s hδσ₀ hδσ₁ hσσ).η = d := sorry

/-- The multiplication of the monad constructed from resolution generators. -/
@[simp, stacks 0G5N "multiplication of the generated monad"]
theorem μ : (EndofunctorResolution.toMonad d s hδσ₀ hδσ₁ hσσ).μ = s := sorry

end toMonad

namespace CosimplicialRealization

/-- Cosimplicial realizations of fixed unit and multiplication formulas are unique. -/
@[stacks 0G5N "uniqueness of an iterated-endofunctor cosimplicial resolution"]
theorem existsUnique {Y : C ⥤ C}
    (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y)
    (hδσ₀ : IteratedEndofunctor.coface d 0 0 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hδσ₁ : IteratedEndofunctor.coface d 0 1 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.codegeneracy s 1 0 ≫
        IteratedEndofunctor.codegeneracy s 0 0 =
      IteratedEndofunctor.codegeneracy s 1 1 ≫
        IteratedEndofunctor.codegeneracy s 0 0) :
    ∃! U : CosimplicialObject (C ⥤ C), CosimplicialRealization d s U := sorry

/-- Any realization of the iterated formulas is the explicit canonical resolution. -/
@[stacks 0G5N "identification with the canonical cosimplicial resolution"]
theorem eq_resolution {Y : C ⥤ C}
    (d : 𝟭 C ⟶ Y) (s : Y ⋙ Y ⟶ Y)
    (hδσ₀ : IteratedEndofunctor.coface d 0 0 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hδσ₁ : IteratedEndofunctor.coface d 0 1 ≫
      IteratedEndofunctor.codegeneracy s 0 0 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.codegeneracy s 1 0 ≫
        IteratedEndofunctor.codegeneracy s 0 0 =
      IteratedEndofunctor.codegeneracy s 1 1 ≫
        IteratedEndofunctor.codegeneracy s 0 0)
    {U : CosimplicialObject (C ⥤ C)} (hU : CosimplicialRealization d s U) :
    U = cosimplicial.resolution d s hδσ₀ hδσ₁ hσσ := sorry

end CosimplicialRealization

end EndofunctorResolution

end CategoryTheory
