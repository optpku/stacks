/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Singleton.Over

/-!
# Simplicial singleton replacements of formal coproducts

This module builds the canonical simplicial singleton-coproduct replacement and its natural map.
It also records the topology-independent degreewise relation for fixed-target formal coproducts.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory
namespace Limits
namespace FormalCoproduct

variable {C : Type u} [Category.{v} C]

namespace Simplicial

/-- Singleton replacement respects identity maps in a simplicial formal coproduct. -/
theorem coproductSingleton_map_id
    (K : SimplicialObject (FormalCoproduct.{w} C))
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.obj Δ).obj]
    (Δ : SimplexCategoryᵒᵖ) :
    FormalCoproduct.coproductSingletonMap (K.map (𝟙 Δ)) =
      𝟙 (FormalCoproduct.coproductSingleton (K.obj Δ)) := sorry

/-- Singleton replacement respects composition in a simplicial formal coproduct. -/
theorem coproductSingleton_map_comp
    (K : SimplicialObject (FormalCoproduct.{w} C))
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.obj Δ).obj]
    {Δ₁ Δ₂ Δ₃ : SimplexCategoryᵒᵖ} (f : Δ₁ ⟶ Δ₂) (g : Δ₂ ⟶ Δ₃) :
    FormalCoproduct.coproductSingletonMap (K.map (f ≫ g)) =
      FormalCoproduct.coproductSingletonMap (K.map f) ≫
        FormalCoproduct.coproductSingletonMap (K.map g) := sorry

/-- Apply singleton-coproduct replacement to every degree and every structure map of a
simplicial formal coproduct. -/
def coproductSingleton
    (K : SimplicialObject (FormalCoproduct.{w} C))
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.obj Δ).obj] :
    SimplicialObject (FormalCoproduct.{w} C) where
  obj Δ := FormalCoproduct.coproductSingleton (K.obj Δ)
  map f := FormalCoproduct.coproductSingletonMap (K.map f)
  map_id Δ := coproductSingleton_map_id K Δ
  map_comp f g := coproductSingleton_map_comp K f g

/-- The object in each degree of `coproductSingleton` is the singleton replacement of
the original degree. -/
@[simp] theorem coproductSingleton_obj
    (K : SimplicialObject (FormalCoproduct.{w} C))
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.obj Δ).obj]
    (Δ : SimplexCategoryᵒᵖ) :
    (Simplicial.coproductSingleton K).obj Δ =
      FormalCoproduct.coproductSingleton (K.obj Δ) := sorry

/-- The structure maps of `coproductSingleton` are induced maps between the
corresponding coproducts. -/
@[simp] theorem coproductSingleton_map
    (K : SimplicialObject (FormalCoproduct.{w} C))
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.obj Δ).obj]
    {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (f : Δ₁ ⟶ Δ₂) :
    (Simplicial.coproductSingleton K).map f =
      FormalCoproduct.coproductSingletonMap (K.map f) := sorry

/-- The canonical maps to singleton replacements commute with every simplicial structure map. -/
theorem toCoproductSingleton_naturality
    (K : SimplicialObject (FormalCoproduct.{w} C))
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.obj Δ).obj]
    {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (f : Δ₁ ⟶ Δ₂) :
    K.map f ≫ FormalCoproduct.toCoproductSingleton (K.obj Δ₂) =
      FormalCoproduct.toCoproductSingleton (K.obj Δ₁) ≫
        FormalCoproduct.coproductSingletonMap (K.map f) := sorry

/-- The canonical degreewise maps assemble into a morphism of simplicial formal coproducts. -/
def toCoproductSingleton
    (K : SimplicialObject (FormalCoproduct.{w} C))
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.obj Δ).obj] :
    K ⟶ Simplicial.coproductSingleton K where
  app Δ := FormalCoproduct.toCoproductSingleton (K.obj Δ)
  naturality _ _ f := toCoproductSingleton_naturality K f

/-- The component of the canonical simplicial morphism is the canonical map to the singleton
replacement in that degree. -/
@[simp] theorem toCoproductSingleton_app
    (K : SimplicialObject (FormalCoproduct.{w} C))
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (K.obj Δ).obj]
    (Δ : SimplexCategoryᵒᵖ) :
    (Simplicial.toCoproductSingleton K).app Δ =
      FormalCoproduct.toCoproductSingleton (K.obj Δ) := sorry

end Simplicial

namespace Over

namespace Simplicial

/-- Fixed-target singleton replacement respects identity maps in a simplicial formal
coproduct. -/
theorem coproductSingleton_map_id {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (CategoryTheory.Over X)))
    [∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun i ↦ ((K.obj Δ).obj i).left)]
    (Δ : SimplexCategoryᵒᵖ) :
    Over.coproductSingletonMap (K.map (𝟙 Δ)) =
      𝟙 (Over.coproductSingleton (K.obj Δ)) := sorry

/-- Fixed-target singleton replacement respects composition in a simplicial formal
coproduct. -/
theorem coproductSingleton_map_comp {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (CategoryTheory.Over X)))
    [∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun i ↦ ((K.obj Δ).obj i).left)]
    {Δ₁ Δ₂ Δ₃ : SimplexCategoryᵒᵖ} (f : Δ₁ ⟶ Δ₂) (g : Δ₂ ⟶ Δ₃) :
    Over.coproductSingletonMap (K.map (f ≫ g)) =
      Over.coproductSingletonMap (K.map f) ≫
        Over.coproductSingletonMap (K.map g) := sorry

/-- Apply fixed-target singleton-coproduct replacement to every degree and structure map of a
simplicial formal coproduct. -/
def coproductSingleton {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (CategoryTheory.Over X)))
    [∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun i ↦ ((K.obj Δ).obj i).left)] :
    SimplicialObject (FormalCoproduct.{w} (CategoryTheory.Over X)) where
  obj Δ := Over.coproductSingleton (K.obj Δ)
  map f := Over.coproductSingletonMap (K.map f)
  map_id Δ := coproductSingleton_map_id K Δ
  map_comp f g := coproductSingleton_map_comp K f g

/-- Each degree of the fixed-target simplicial singleton replacement is the singleton family on
the coproduct of the source objects in that degree. -/
@[simp] theorem coproductSingleton_obj {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (CategoryTheory.Over X)))
    [∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun i ↦ ((K.obj Δ).obj i).left)]
    (Δ : SimplexCategoryᵒᵖ) :
    (coproductSingleton K).obj Δ = Over.coproductSingleton (K.obj Δ) := sorry

/-- Each structure map of the fixed-target simplicial singleton replacement is the map induced
between the corresponding source coproducts. -/
@[simp] theorem coproductSingleton_map {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (CategoryTheory.Over X)))
    [∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun i ↦ ((K.obj Δ).obj i).left)]
    {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (f : Δ₁ ⟶ Δ₂) :
    (coproductSingleton K).map f = Over.coproductSingletonMap (K.map f) := sorry

/-- The canonical fixed-target singleton maps commute with every simplicial structure map. -/
theorem toCoproductSingleton_naturality {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (CategoryTheory.Over X)))
    [∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun i ↦ ((K.obj Δ).obj i).left)]
    {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (f : Δ₁ ⟶ Δ₂) :
    K.map f ≫ Over.toCoproductSingleton (K.obj Δ₂) =
      Over.toCoproductSingleton (K.obj Δ₁) ≫
        Over.coproductSingletonMap (K.map f) := sorry

/-- The degreewise maps to fixed-target singleton replacements assemble into a simplicial
morphism. -/
def toCoproductSingleton {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (CategoryTheory.Over X)))
    [∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun i ↦ ((K.obj Δ).obj i).left)] :
    K ⟶ coproductSingleton K where
  app Δ := Over.toCoproductSingleton (K.obj Δ)
  naturality _ _ f := toCoproductSingleton_naturality K f

/-- A component of the canonical fixed-target simplicial morphism is the degreewise coproduct
map. -/
@[simp] theorem toCoproductSingleton_app {X : C}
    (K : SimplicialObject (FormalCoproduct.{w} (CategoryTheory.Over X)))
    [∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct (fun i ↦ ((K.obj Δ).obj i).left)]
    (Δ : SimplexCategoryᵒᵖ) :
    (toCoproductSingleton K).app Δ =
      Over.toCoproductSingleton (K.obj Δ) := sorry

end Simplicial

end Over
end FormalCoproduct
end Limits
end CategoryTheory
