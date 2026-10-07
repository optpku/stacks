module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Singleton replacements of formal coproducts

This module turns an indexed formal coproduct into the singleton formal coproduct whose sole
member is the coproduct of its members.  The construction and its canonical map are independent
of sites, presheaves, and slice categories.
-/

@[expose] public section

universe w v u

namespace CategoryTheory
namespace Limits
namespace FormalCoproduct

noncomputable section

variable {C : Type u} [Category.{v} C]

/-- Replace a formal coproduct by the singleton family on the coproduct of its members. -/
def coproductSingleton (K : FormalCoproduct.{w} C) [HasCoproduct K.obj] :
    FormalCoproduct.{w} C where
  I := PUnit
  obj := fun _ ↦ ∐ K.obj

/-- Unfolding the singleton replacement gives the singleton family on the coproduct object. -/
theorem coproductSingleton_def (K : FormalCoproduct.{w} C) [HasCoproduct K.obj] :
    coproductSingleton K =
      { I := PUnit
        obj := fun _ ↦ ∐ K.obj } := sorry

/-- The singleton replacement has `PUnit` as its indexing type. -/
@[simp]
theorem coproductSingleton_index (K : FormalCoproduct.{w} C) [HasCoproduct K.obj] :
    (coproductSingleton K).I = PUnit := sorry

/-- The sole member of the singleton replacement is the coproduct of the original members. -/
@[simp]
theorem coproductSingleton_obj (K : FormalCoproduct.{w} C) [HasCoproduct K.obj]
    (p : PUnit) :
    (coproductSingleton K).obj p = ∐ K.obj := sorry

/-- The map between coproduct objects induced by a morphism of formal coproducts. -/
@[stacks 0DB0 "map on coproduct realizations"]
def coproductMap {K L : FormalCoproduct.{w} C} [HasCoproduct K.obj]
    [HasCoproduct L.obj] (φ : K ⟶ L) :
    (∐ K.obj) ⟶ ∐ L.obj :=
  Sigma.map' φ.f φ.φ

/-- A coproduct inclusion followed by `coproductMap` is the corresponding component map
followed by its target coproduct inclusion. -/
@[simp]
theorem ι_coproductMap {K L : FormalCoproduct.{w} C} [HasCoproduct K.obj]
    [HasCoproduct L.obj] (φ : K ⟶ L) (i : K.I) :
    Sigma.ι K.obj i ≫ coproductMap φ = φ.φ i ≫ Sigma.ι L.obj (φ.f i) := sorry

/-- The coproduct map induced by an identity formal-coproduct morphism is the identity. -/
@[simp]
theorem coproductMap_id (K : FormalCoproduct.{w} C) [HasCoproduct K.obj] :
    coproductMap (𝟙 K) = 𝟙 (∐ K.obj) := sorry

/-- Coproduct maps respect composition of formal-coproduct morphisms. -/
@[simp]
theorem coproductMap_comp {K L M : FormalCoproduct.{w} C}
    [HasCoproduct K.obj] [HasCoproduct L.obj] [HasCoproduct M.obj]
    (φ : K ⟶ L) (ψ : L ⟶ M) :
    coproductMap (φ ≫ ψ) = coproductMap φ ≫ coproductMap ψ := sorry

/-- The canonical map from a formal coproduct to its singleton coproduct replacement. -/
def toCoproductSingleton (K : FormalCoproduct.{w} C) [HasCoproduct K.obj] :
    K ⟶ coproductSingleton K where
  f := fun _ ↦ PUnit.unit
  φ := fun i ↦ Sigma.ι K.obj i

/-- The morphism between singleton replacements induced by a morphism of formal coproducts. -/
def coproductSingletonMap {K L : FormalCoproduct.{w} C} [HasCoproduct K.obj]
    [HasCoproduct L.obj] (φ : K ⟶ L) :
    coproductSingleton K ⟶ coproductSingleton L where
  f := fun _ ↦ PUnit.unit
  φ := fun _ ↦ coproductMap φ

/-- The singleton-replacement map has the unique possible map of singleton index types. -/
@[simp]
theorem coproductSingletonMap_f {K L : FormalCoproduct.{w} C} [HasCoproduct K.obj]
    [HasCoproduct L.obj] (φ : K ⟶ L) (p : PUnit) :
    (coproductSingletonMap φ).f p = PUnit.unit := sorry

/-- The sole component of a singleton-replacement map is the coproduct map induced by the
original formal-coproduct morphism. -/
@[simp]
theorem coproductSingletonMap_φ {K L : FormalCoproduct.{w} C} [HasCoproduct K.obj]
    [HasCoproduct L.obj] (φ : K ⟶ L) (p : PUnit) :
    (coproductSingletonMap φ).φ p = coproductMap φ := sorry

/-- The canonical maps to singleton replacements are natural in a formal-coproduct morphism. -/
theorem toCoproductSingleton_naturality {K L : FormalCoproduct.{w} C} [HasCoproduct K.obj]
    [HasCoproduct L.obj] (φ : K ⟶ L) :
    toCoproductSingleton K ≫ coproductSingletonMap φ =
      φ ≫ toCoproductSingleton L := sorry

/-- The singleton-replacement map induced by an identity morphism is the identity. -/
@[simp]
theorem coproductSingletonMap_id (K : FormalCoproduct.{w} C) [HasCoproduct K.obj] :
    coproductSingletonMap (𝟙 K) = 𝟙 (coproductSingleton K) := sorry

/-- Singleton replacement carries composition of formal-coproduct morphisms to composition. -/
@[simp]
theorem coproductSingletonMap_comp {K L M : FormalCoproduct.{w} C}
    [HasCoproduct K.obj] [HasCoproduct L.obj] [HasCoproduct M.obj]
    (φ : K ⟶ L) (ψ : L ⟶ M) :
    coproductSingletonMap (φ ≫ ψ) = coproductSingletonMap φ ≫ coproductSingletonMap ψ := sorry

/-- The canonical map to the singleton replacement sends every index to its unique index. -/
@[simp]
theorem toCoproductSingleton_f (K : FormalCoproduct.{w} C) [HasCoproduct K.obj]
    (i : K.I) :
    (toCoproductSingleton K).f i = PUnit.unit := sorry

/-- The component of the canonical map to the singleton replacement is the corresponding
coproduct inclusion. -/
@[simp]
theorem toCoproductSingleton_φ (K : FormalCoproduct.{w} C) [HasCoproduct K.obj]
    (i : K.I) :
    (toCoproductSingleton K).φ i = Sigma.ι K.obj i := sorry

/-- Transport the canonical map to the singleton replacement along a chosen equality with a
target formal coproduct. -/
def toCoproductSingletonOfEq (K L : FormalCoproduct.{w} C) [HasCoproduct K.obj]
    (hL : coproductSingleton K = L) :
    K ⟶ L :=
  toCoproductSingleton K ≫ eqToHom hL

/-- If the selected target is definitionally the singleton replacement, the transported map is
the canonical singleton-replacement map. -/
@[simp]
theorem toCoproductSingletonOfEq_rfl (K : FormalCoproduct.{w} C)
    [HasCoproduct K.obj] :
    toCoproductSingletonOfEq K (coproductSingleton K) rfl = toCoproductSingleton K := sorry

end

end FormalCoproduct
end Limits
end CategoryTheory
