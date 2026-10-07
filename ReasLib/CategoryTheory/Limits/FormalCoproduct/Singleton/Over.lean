module

public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Over
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Singleton

/-!
# Singleton replacements of fixed-target formal coproducts

This module gives the singleton-coproduct replacement for formal coproducts in a slice category.
It only assumes a coproduct of the underlying source objects, and constructs the induced arrow to
the fixed target directly.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory
namespace Limits
namespace FormalCoproduct
namespace Over

variable {C : Type u} [Category.{v} C]

/-- Replace a fixed-target formal coproduct by the singleton family on the coproduct of its source
objects, equipped with the induced arrow to the common target. -/
def coproductSingleton {X : C} (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    [HasCoproduct (fun i ↦ (K.obj i).left)] :
    FormalCoproduct.{w} (CategoryTheory.Over X) :=
  ofArrows
    (fun _ : PUnit ↦ ∐ fun i ↦ (K.obj i).left)
    (fun _ ↦ Sigma.desc fun i ↦ (K.obj i).hom)

/-- Unfolding the fixed-target singleton replacement gives the singleton arrow family induced by
the coproduct descent map to the common target. -/
theorem coproductSingleton_def {X : C} (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    [HasCoproduct (fun i ↦ (K.obj i).left)] :
    coproductSingleton K =
      ofArrows
        (fun _ : PUnit ↦ ∐ fun i ↦ (K.obj i).left)
        (fun _ ↦ Sigma.desc fun i ↦ (K.obj i).hom) := sorry

/-- The fixed-target singleton replacement has `PUnit` as its indexing type. -/
@[simp]
theorem coproductSingleton_index {X : C} (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    [HasCoproduct (fun i ↦ (K.obj i).left)] :
    (coproductSingleton K).I = PUnit := sorry

/-- The source object of the sole fixed-target singleton member is the coproduct of the original
source objects. -/
@[simp]
theorem coproductSingleton_obj_left {X : C}
    (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    [HasCoproduct (fun i ↦ (K.obj i).left)] (p : PUnit) :
    ((coproductSingleton K).obj p).left = ∐ fun i ↦ (K.obj i).left := sorry

/-- The structure map of the sole fixed-target singleton member is induced by the original
component structure maps. -/
@[simp]
theorem coproductSingleton_obj_hom {X : C}
    (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    [HasCoproduct (fun i ↦ (K.obj i).left)] (p : PUnit) :
    ((coproductSingleton K).obj p).hom = Sigma.desc fun i ↦ (K.obj i).hom := sorry

/-- Forgetting the target from the fixed-target singleton replacement gives the ordinary singleton
family on the coproduct of the underlying source objects. -/
@[simp]
theorem forgetOver_obj_coproductSingleton {X : C}
    (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    [HasCoproduct (fun i ↦ (K.obj i).left)] :
    (forgetOver X).obj (coproductSingleton K) =
      { I := PUnit
        obj := fun _ ↦ ∐ fun i ↦ (K.obj i).left } := sorry

/-- The underlying coproduct map induced by a fixed-target formal-coproduct morphism. -/
def coproductSingletonMapLeft {X : C}
    {K L : FormalCoproduct.{w} (CategoryTheory.Over X)}
    [HasCoproduct (fun i ↦ (K.obj i).left)] [HasCoproduct (fun i ↦ (L.obj i).left)]
    (φ : K ⟶ L) :
    (∐ fun i ↦ (K.obj i).left) ⟶ ∐ fun i ↦ (L.obj i).left :=
  Sigma.map' φ.f fun i ↦ (φ.φ i).left

/-- The underlying singleton-replacement map sends a source coproduct inclusion through the
corresponding component and target coproduct inclusion. -/
@[simp]
theorem coproductSingletonMapLeft_ι {X : C}
    {K L : FormalCoproduct.{w} (CategoryTheory.Over X)}
    [HasCoproduct (fun i ↦ (K.obj i).left)] [HasCoproduct (fun i ↦ (L.obj i).left)]
    (φ : K ⟶ L) (i : K.I) :
    Sigma.ι (fun j ↦ (K.obj j).left) i ≫ coproductSingletonMapLeft φ =
      (φ.φ i).left ≫ Sigma.ι (fun j ↦ (L.obj j).left) (φ.f i) := sorry

/-- The underlying coproduct map induced by a fixed-target formal-coproduct morphism commutes
with the induced maps from the source coproducts to the common target. -/
theorem coproductSingletonMap_comm {X : C}
    {K L : FormalCoproduct.{w} (CategoryTheory.Over X)}
    [HasCoproduct (fun i ↦ (K.obj i).left)] [HasCoproduct (fun i ↦ (L.obj i).left)]
    (φ : K ⟶ L) :
    coproductSingletonMapLeft φ ≫ Sigma.desc (fun j ↦ (L.obj j).hom) =
      Sigma.desc (fun i ↦ (K.obj i).hom) := sorry

/-- The morphism between fixed-target singleton replacements induced by a morphism of formal
coproducts over the same target. -/
def coproductSingletonMap {X : C}
    {K L : FormalCoproduct.{w} (CategoryTheory.Over X)}
    [HasCoproduct (fun i ↦ (K.obj i).left)] [HasCoproduct (fun i ↦ (L.obj i).left)]
    (φ : K ⟶ L) :
    coproductSingleton K ⟶ coproductSingleton L where
  f := fun _ ↦ PUnit.unit
  φ := fun _ ↦
    CategoryTheory.Over.homMk
      (coproductSingletonMapLeft φ)
      (coproductSingletonMap_comm φ)

/-- The fixed-target singleton-replacement map has the unique possible map of singleton index
types. -/
@[simp]
theorem coproductSingletonMap_f {X : C}
    {K L : FormalCoproduct.{w} (CategoryTheory.Over X)}
    [HasCoproduct (fun i ↦ (K.obj i).left)] [HasCoproduct (fun i ↦ (L.obj i).left)]
    (φ : K ⟶ L) (p : PUnit) :
    (coproductSingletonMap φ).f p = PUnit.unit := sorry

/-- The underlying component of a fixed-target singleton-replacement map is the coproduct map
induced by the original formal-coproduct morphism. -/
@[simp]
theorem coproductSingletonMap_φ_left {X : C}
    {K L : FormalCoproduct.{w} (CategoryTheory.Over X)}
    [HasCoproduct (fun i ↦ (K.obj i).left)] [HasCoproduct (fun i ↦ (L.obj i).left)]
    (φ : K ⟶ L) (p : PUnit) :
    ((coproductSingletonMap φ).φ p).left = coproductSingletonMapLeft φ := sorry

/-- The fixed-target singleton-replacement map induced by an identity is the identity. -/
@[simp]
theorem coproductSingletonMap_id {X : C}
    (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    [HasCoproduct (fun i ↦ (K.obj i).left)] :
    coproductSingletonMap (𝟙 K) = 𝟙 (coproductSingleton K) := sorry

/-- Fixed-target singleton replacement carries composition of formal-coproduct morphisms to
composition. -/
@[simp]
theorem coproductSingletonMap_comp {X : C}
    {K L M : FormalCoproduct.{w} (CategoryTheory.Over X)}
    [HasCoproduct (fun i ↦ (K.obj i).left)] [HasCoproduct (fun i ↦ (L.obj i).left)]
    [HasCoproduct (fun i ↦ (M.obj i).left)]
    (φ : K ⟶ L) (ψ : L ⟶ M) :
    coproductSingletonMap (φ ≫ ψ) = coproductSingletonMap φ ≫ coproductSingletonMap ψ := sorry

/-- The canonical fixed-target map from a family to its singleton-coproduct replacement. -/
def toCoproductSingleton {X : C} (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    [HasCoproduct (fun i ↦ (K.obj i).left)] :
    K ⟶ coproductSingleton K where
  f := fun _ ↦ PUnit.unit
  φ := fun i ↦
    CategoryTheory.Over.homMk
      (Sigma.ι (fun j ↦ (K.obj j).left) i)
      (Sigma.ι_desc (fun j ↦ (K.obj j).hom) i)

/-- The canonical fixed-target map sends every index to the unique singleton index. -/
@[simp]
theorem toCoproductSingleton_f {X : C}
    (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    [HasCoproduct (fun i ↦ (K.obj i).left)] (i : K.I) :
    (toCoproductSingleton K).f i = PUnit.unit := sorry

/-- The underlying component of the canonical fixed-target singleton map is the relevant
coproduct inclusion. -/
@[simp]
theorem toCoproductSingleton_φ_left {X : C}
    (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    [HasCoproduct (fun i ↦ (K.obj i).left)] (i : K.I) :
    ((toCoproductSingleton K).φ i).left = Sigma.ι (fun j ↦ (K.obj j).left) i := sorry

/-- The canonical fixed-target maps to singleton replacements are natural in a
formal-coproduct morphism. -/
theorem toCoproductSingleton_naturality {X : C}
    {K L : FormalCoproduct.{w} (CategoryTheory.Over X)}
    [HasCoproduct (fun i ↦ (K.obj i).left)] [HasCoproduct (fun i ↦ (L.obj i).left)]
    (φ : K ⟶ L) :
    toCoproductSingleton K ≫ coproductSingletonMap φ =
      φ ≫ toCoproductSingleton L := sorry

/-- Transport the canonical fixed-target singleton map along a chosen equality with a target
formal coproduct. -/
def toCoproductSingletonOfEq {X : C}
    (K L : FormalCoproduct.{w} (CategoryTheory.Over X))
    [HasCoproduct (fun i ↦ (K.obj i).left)] (hL : coproductSingleton K = L) :
    K ⟶ L :=
  toCoproductSingleton K ≫ eqToHom hL

/-- Forgetting a canonical fixed-target singleton map preserves its unique target index. -/
@[simp]
theorem forgetOver_map_toCoproductSingleton_f {X : C}
    (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    [HasCoproduct (fun i ↦ (K.obj i).left)] (i : K.I) :
    ((forgetOver X).map (toCoproductSingleton K)).f i = PUnit.unit := sorry

/-- Forgetting a canonical fixed-target singleton map sends each source component by its
corresponding coproduct inclusion. -/
@[simp]
theorem forgetOver_map_toCoproductSingleton_φ {X : C}
    (K : FormalCoproduct.{w} (CategoryTheory.Over X))
    [HasCoproduct (fun i ↦ (K.obj i).left)] (i : K.I) :
    ((forgetOver X).map (toCoproductSingleton K)).φ i =
      Sigma.ι (fun j ↦ (K.obj j).left) i := sorry

end Over
end FormalCoproduct
end Limits
end CategoryTheory
