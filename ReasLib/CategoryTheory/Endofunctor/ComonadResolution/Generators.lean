/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.Realization
public import ReasLib.AlgebraicTopology.SimplexCategory.HomCode
public import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Generator presentations of comonad resolutions

Typed simplex generator words evaluate to maps between positive endofunctor iterates. The three
degree-zero relations bundle raw counit and comultiplication data into a Mathlib `Comonad` and
construct the corresponding source-facing simplicial resolution.
-/

@[expose] public section

open Opposite
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Augmentation
open CategoryTheory.Functor
open scoped CategoryTheory.IteratedEndofunctor Simplicial

universe v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace EndofunctorResolution

namespace simplicial

/-- Evaluate a simplex generator code by inserting the specified counit-like and
comultiplication-like transformations. -/
@[stacks 0G5N "generator-code evaluation"]
def evalCode {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) :
    {m n : ℕ} → SimplexCategory.HomCode m n → (Y ⁺⦋n⦌ ⟶ Y ⁺⦋m⦌)
  | _, _, .id _ => 𝟙 _
  | _, _, .face i code => IteratedEndofunctor.face d _ i ≫ evalCode d s code
  | _, _, .degeneracy i code => evalCode d s code ≫ IteratedEndofunctor.degeneracy s _ i

/-- Generator words representing the same simplex morphism have the same evaluation whenever
the counit-like and comultiplication-like maps satisfy the comonad identities. -/
@[stacks 0G5N "generator-code evaluation independence"]
theorem evalCode.eq_of_toHom_eq {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₀ : IteratedEndofunctor.degeneracy s 0 0 ≫
      IteratedEndofunctor.face d 0 0 = 𝟙 Y)
    (hσδ₁ : IteratedEndofunctor.degeneracy s 0 0 ≫
      IteratedEndofunctor.face d 0 1 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.degeneracy s 0 0 ≫
        IteratedEndofunctor.degeneracy s 1 0 =
      IteratedEndofunctor.degeneracy s 0 0 ≫
        IteratedEndofunctor.degeneracy s 1 1)
    {m n : ℕ} (a b : SimplexCategory.HomCode m n)
    (h : a.toHom = b.toHom) :
    evalCode d s a = evalCode d s b := sorry

/-- The computational action of the iterated-endofunctor resolution on a simplex morphism.
The chosen code is proof-independent; `map.eq_evalCode` gives semantic independence from the
chosen representation under the comonad identities. -/
@[stacks 0G5N "iterated-endofunctor resolution map"]
noncomputable def map {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y) {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') :
    Y ⁺⦋Δ.unop.len⦌ ⟶ Y ⁺⦋Δ'.unop.len⦌ :=
  evalCode d s
    (SimplexCategory.HomCode.ofHom Δ'.unop.len Δ.unop.len
      (SimplexCategory.canonicalHom θ))

/-- The canonical resolution map may be computed from any generator word representing the
canonical skeletal form of the simplex morphism. -/
@[stacks 0G5N "resolution map from any generator code"]
theorem map.eq_evalCode {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₀ : IteratedEndofunctor.degeneracy s 0 0 ≫
      IteratedEndofunctor.face d 0 0 = 𝟙 Y)
    (hσδ₁ : IteratedEndofunctor.degeneracy s 0 0 ≫
      IteratedEndofunctor.face d 0 1 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.degeneracy s 0 0 ≫
        IteratedEndofunctor.degeneracy s 1 0 =
      IteratedEndofunctor.degeneracy s 0 0 ≫
        IteratedEndofunctor.degeneracy s 1 1)
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ')
    (code : SimplexCategory.HomCode Δ'.unop.len Δ.unop.len)
    (hcode : code.toHom = SimplexCategory.canonicalHom θ) :
    map d s θ = evalCode d s code := sorry

end simplicial

/-- A realization evaluates every simplex morphism by the canonical generator-code map, after
transport along its object identifications. -/
@[stacks 0G5N "realization map formula"]
theorem Realization.map.eq {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
    {U : SimplicialObject (C ⥤ C)} (hU : Realization d s U)
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') :
    (hU.objIso Δ.unop.len).hom ≫ simplicial.map d s θ =
      U.map θ ≫ (hU.objIso Δ'.unop.len).hom := sorry

/-- The objectwise coassociativity law extracted from the generator presentation. -/
@[stacks 0G5N "generator coassociativity in components"]
theorem generators.coassoc.app {Y : C ⥤ C} (s : Y ⟶ Y ⋙ Y)
    (hσσ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 0 =
      IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 1) (X : C) :
    s.app X ≫ Y.map (s.app X) = s.app X ≫ s.app (Y.obj X) := sorry

/-- The objectwise left counit law extracted from the generator presentation. -/
@[stacks 0G5N "generator left counit in components"]
theorem generators.left_counit.app {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₁ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 1 = 𝟙 Y) (X : C) :
    s.app X ≫ d.app (Y.obj X) = 𝟙 (Y.obj X) := sorry

/-- The objectwise right counit law extracted from the generator presentation. -/
@[stacks 0G5N "generator right counit in components"]
theorem generators.right_counit.app {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₀ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 0 = 𝟙 Y) (X : C) :
    s.app X ≫ Y.map (d.app X) = 𝟙 (Y.obj X) := sorry

/-- Turn raw resolution generators and their degree-zero identities into the canonical
Mathlib `Comonad` owner.  Downstream constructions should consume the resulting comonad. -/
@[stacks 0G5N "comonad from iterated-endofunctor generators"]
def toComonad {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₀ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 0 = 𝟙 Y)
    (hσδ₁ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 1 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 0 =
      IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 1) : Comonad C where
  toFunctor := Y
  ε := d
  δ := s
  coassoc := generators.coassoc.app s hσσ
  left_counit := generators.left_counit.app d s hσδ₁
  right_counit := generators.right_counit.app d s hσδ₀

namespace toComonad

variable {Y : C ⥤ C} (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
variable
  (hσδ₀ : IteratedEndofunctor.degeneracy s 0 0 ≫
    IteratedEndofunctor.face d 0 0 = 𝟙 Y)
  (hσδ₁ : IteratedEndofunctor.degeneracy s 0 0 ≫
    IteratedEndofunctor.face d 0 1 = 𝟙 Y)
  (hσσ : IteratedEndofunctor.degeneracy s 0 0 ≫
      IteratedEndofunctor.degeneracy s 1 0 =
    IteratedEndofunctor.degeneracy s 0 0 ≫
      IteratedEndofunctor.degeneracy s 1 1)

/-- The endofunctor underlying the comonad constructed from resolution generators. -/
@[simp, stacks 0G5N "underlying endofunctor of the generated comonad"]
theorem coe :
    (EndofunctorResolution.toComonad d s hσδ₀ hσδ₁ hσσ : C ⥤ C) = Y := sorry

/-- The counit of the comonad constructed from resolution generators. -/
@[simp, stacks 0G5N "counit of the generated comonad"]
theorem ε :
    (EndofunctorResolution.toComonad d s hσδ₀ hσδ₁ hσσ).ε = d := sorry

/-- The comultiplication of the comonad constructed from resolution generators. -/
@[simp, stacks 0G5N "comultiplication of the generated comonad"]
theorem δ :
    (EndofunctorResolution.toComonad d s hσδ₀ hσδ₁ hσσ).δ = s := sorry

end toComonad

namespace simplicial

/-- The canonical resolution map preserves identity simplex morphisms under the two counit laws
and coassociativity law. -/
@[stacks 0G5N "resolution map preserves identities"]
theorem map.id {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₀ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 0 = 𝟙 Y)
    (hσδ₁ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 1 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 0 =
      IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 1)
    (Δ : SimplexCategoryᵒᵖ) :
    map d s (𝟙 Δ) = 𝟙 _ := sorry

/-- The canonical resolution map preserves composition under the two counit laws and
coassociativity law. -/
@[stacks 0G5N "resolution map preserves composition"]
theorem map.comp {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₀ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 0 = 𝟙 Y)
    (hσδ₁ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 1 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 0 =
      IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 1)
    {Δ₀ Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (θ₁ : Δ₀ ⟶ Δ₁) (θ₂ : Δ₁ ⟶ Δ₂) :
    map d s (θ₁ ≫ θ₂) =
      map d s θ₁ ≫ map d s θ₂ := sorry

/-- The explicit simplicial object generated by counit-like and comultiplication-like maps
satisfying the two counit laws and coassociativity. Its object and map fields are computed by
`IteratedEndofunctor.obj` and `EndofunctorResolution.simplicial.map`. -/
@[stacks 0G5N "iterated-endofunctor resolution"]
noncomputable def resolution {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₀ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 0 = 𝟙 Y)
    (hσδ₁ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 1 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 0 =
      IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 1) :
    SimplicialObject (C ⥤ C) where
  obj Δ := Y ⁺⦋Δ.unop.len⦌
  map θ := map d s θ
  map_id := map.id d s hσδ₀ hσδ₁ hσσ
  map_comp := map.comp d s hσδ₀ hσδ₁ hσσ

/-- The object field of the explicit resolution computes to the corresponding positive
iterate. -/
@[simp, stacks 0G5N "raw resolution object formula"]
theorem resolution.obj {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₀ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 0 = 𝟙 Y)
    (hσδ₁ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 1 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 0 =
      IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 1)
    (Δ : SimplexCategoryᵒᵖ) :
    (resolution d s hσδ₀ hσδ₁ hσσ).obj Δ =
      Y ⁺⦋Δ.unop.len⦌ := sorry

/-- The map field of the explicit resolution is the canonical generator-code evaluation. -/
@[simp, stacks 0G5N "raw resolution map formula"]
theorem resolution.map {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₀ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 0 = 𝟙 Y)
    (hσδ₁ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 1 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 0 =
      IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 1)
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') :
    (resolution d s hσδ₀ hσδ₁ hσσ).map θ =
      map d s θ := sorry

/-- The explicit iterated-endofunctor resolution satisfies its object, face, and degeneracy
formulas. -/
@[stacks 0G5N "raw resolution realization formulas"]
theorem resolution.realization {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₀ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 0 = 𝟙 Y)
    (hσδ₁ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 1 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 0 =
      IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 1) :
    Realization d s
      (resolution d s hσδ₀ hσδ₁ hσσ) := sorry

end simplicial

namespace Realization

/-- Simplicial realizations of fixed iterated-endofunctor face and degeneracy formulas are
unique. -/
@[stacks 0G5N "uniqueness of an iterated-endofunctor resolution"]
theorem existsUnique {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₀ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 0 = 𝟙 Y)
    (hσδ₁ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 1 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 0 =
      IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 1) :
    ∃! U : SimplicialObject (C ⥤ C), Realization d s U := sorry

/-- Any realization of the iterated-endofunctor formulas is equal to the explicit canonical
resolution. -/
@[stacks 0G5N "identification with the canonical resolution"]
theorem eq_resolution {Y : C ⥤ C}
    (d : Y ⟶ 𝟭 C) (s : Y ⟶ Y ⋙ Y)
    (hσδ₀ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 0 = 𝟙 Y)
    (hσδ₁ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.face d 0 1 = 𝟙 Y)
    (hσσ : IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 0 =
      IteratedEndofunctor.degeneracy s 0 0 ≫ IteratedEndofunctor.degeneracy s 1 1)
    {U : SimplicialObject (C ⥤ C)} (hU : Realization d s U) :
    U = simplicial.resolution d s hσδ₀ hσδ₁ hσσ := sorry

end Realization

end EndofunctorResolution

end CategoryTheory
