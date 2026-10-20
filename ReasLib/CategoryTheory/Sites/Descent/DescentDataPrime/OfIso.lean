module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Descent data from comparison isomorphisms

The cocycle condition on invertible pairwise comparisons implies diagonal normalization
and therefore determines descent data for a Cat-valued pseudofunctor.
-/

@[expose] public section

universe u v u' v' t

namespace CategoryTheory.Pseudofunctor.DescentData'

open Opposite Limits

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  (sq : ∀ i j, ChosenPullback (f i) (f j))
  (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
  (obj : ∀ i, F.obj (.mk (op (X i))))

section

variable (hom : ∀ i j,
  (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
    (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))

/-- Pairwise comparison morphisms satisfy the cocycle condition when their pullbacks
compose on every chosen triple overlap. -/
def IsCocycle : Prop :=
  ∀ i j k,
    pullHom' (F := F) (f := f) (sq := sq) (obj := obj) (obj' := obj)
        hom (sq₃ i j k).p (i₁ := i) (i₂ := j)
        (sq₃ i j k).p₁ (sq₃ i j k).p₂ (sq₃ i j k).w₁ (sq₃ i j k).w₂ ≫
      pullHom' (F := F) (f := f) (sq := sq) (obj := obj) (obj' := obj)
        hom (sq₃ i j k).p (i₁ := j) (i₂ := k)
        (sq₃ i j k).p₂ (sq₃ i j k).p₃ (sq₃ i j k).w₂ (sq₃ i j k).w₃ =
      pullHom' (F := F) (f := f) (sq := sq) (obj := obj) (obj' := obj)
        hom (sq₃ i j k).p (i₁ := i) (i₂ := k)
        (sq₃ i j k).p₁ (sq₃ i j k).p₃ (sq₃ i j k).w₁ (sq₃ i j k).w₃

/-- The cocycle condition is exactly the composition equation on each triple overlap. -/
theorem isCocycle_iff :
    IsCocycle F sq sq₃ obj hom ↔ ∀ i j k,
      pullHom' (F := F) (f := f) (sq := sq) (obj := obj) (obj' := obj)
          hom (sq₃ i j k).p (i₁ := i) (i₂ := j)
          (sq₃ i j k).p₁ (sq₃ i j k).p₂ (sq₃ i j k).w₁ (sq₃ i j k).w₂ ≫
        pullHom' (F := F) (f := f) (sq := sq) (obj := obj) (obj' := obj)
          hom (sq₃ i j k).p (i₁ := j) (i₂ := k)
          (sq₃ i j k).p₂ (sq₃ i j k).p₃ (sq₃ i j k).w₂ (sq₃ i j k).w₃ =
        pullHom' (F := F) (f := f) (sq := sq) (obj := obj) (obj' := obj)
          hom (sq₃ i j k).p (i₁ := i) (i₂ := k)
          (sq₃ i j k).p₁ (sq₃ i j k).p₃ (sq₃ i j k).w₁ (sq₃ i j k).w₃ := Iff.rfl

/-- Pairwise comparison morphisms are normalized at an index when their diagonal pullback
is the identity of the corresponding pullback object. -/
def IsNormalizedAt (i : ι) : Prop :=
  pullHom' (F := F) (f := f) (sq := sq) (obj := obj) (obj' := obj)
    hom (f i) (i₁ := i) (i₂ := i) (𝟙 (X i)) (𝟙 (X i))
    (Category.id_comp (f i)) (Category.id_comp (f i)) = 𝟙 _

/-- Normalization at an index is exactly the diagonal identity equation. -/
theorem isNormalizedAt_iff (i : ι) :
    IsNormalizedAt F sq obj hom i ↔
      pullHom' (F := F) (f := f) (sq := sq) (obj := obj) (obj' := obj)
        hom (f i) (i₁ := i) (i₂ := i) (𝟙 (X i)) (𝟙 (X i))
        (Category.id_comp (f i)) (Category.id_comp (f i)) = 𝟙 _ := Iff.rfl

end

variable (φ : ∀ i j,
  (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
    (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
  (hφ : IsCocycle F sq sq₃ obj (fun i j ↦ (φ i j).hom))

include hφ in
/-- Invertible pairwise comparisons satisfying the cocycle condition are normalized
at every index. -/
theorem ofIso_self (i : ι) :
    IsNormalizedAt F sq obj (fun a b ↦ (φ a b).hom) i := sorry

/-- Component objects and invertible pairwise comparisons satisfying the cocycle condition
determine descent data on the chosen overlaps. -/
def ofIso : F.DescentData' sq sq₃ where
  obj := obj
  hom i j := (φ i j).hom
  pullHom'_hom_self i :=
    (isNormalizedAt_iff F sq obj (fun a b ↦ (φ a b).hom) i).mp
      (ofIso_self F sq sq₃ obj φ hφ i)
  pullHom'_hom_comp := (isCocycle_iff F sq sq₃ obj (fun a b ↦ (φ a b).hom)).mp hφ

/-- The component objects of descent data constructed from isomorphisms are the
supplied objects. -/
theorem ofIso_obj (i : ι) : (ofIso F sq sq₃ obj φ hφ).obj i = obj i := rfl

/-- The comparison morphisms of descent data constructed from isomorphisms are the
forward maps of the supplied isomorphisms. -/
theorem ofIso_hom (i j : ι) :
    (ofIso F sq sq₃ obj φ hφ).hom i j = (φ i j).hom := rfl

end CategoryTheory.Pseudofunctor.DescentData'
