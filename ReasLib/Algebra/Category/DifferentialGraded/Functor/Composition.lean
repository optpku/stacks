/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of Differential Graded Functors

This leaf owns the strict identity and composition operations on the
enrichment-level `DgFunctor` structure.  It deliberately stops before the
induced functors on closed morphisms and homotopy categories.
-/

@[expose] public section

namespace DifferentialGradedCategory

open scoped DifferentialGradedCategory

universe u v w z t

namespace DgFunctor

variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w} {C : Type z} {D : Type t}
variable [DA : DifferentialGradedCategory R A]
variable [DB : DifferentialGradedCategory R B]
variable [DC : DifferentialGradedCategory R C]
variable [DD : DifferentialGradedCategory R D]

/-- The identity differential graded functor on a differential graded category. -/
@[stacks 09L6 "identity differential graded functor"]
def id (R : Type u) [CommRing R] (A : Type v) [DifferentialGradedCategory R A] :
    DgFunctor R A A where
  obj := fun X ↦ X
  map := fun f ↦ f
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_d _ := rfl
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The identity DG functor leaves objects unchanged. -/
@[simp, stacks 09L6 "identity DG functor on objects"]
theorem id_obj (X : A) : (id R A).obj X = X := rfl

/-- The identity DG functor leaves every homogeneous morphism unchanged. -/
@[simp, stacks 09L6 "identity DG functor on homogeneous morphisms"]
theorem id_map {X Y : A} {n : ℤ} (f : X ⟶[n] Y) : (id R A).map f = f := rfl

/-- The composite of two differential graded functors. -/
@[stacks 09L6 "composition of differential graded functors"]
def comp (G : DgFunctor R B C) (F : DgFunctor R A B) : DgFunctor R A C where
  obj := fun X ↦ G.obj (F.obj X)
  map := fun f ↦ G.map (F.map f)
  map_add f g := by rw [F.map_add, G.map_add]
  map_smul r f := by rw [F.map_smul, G.map_smul]
  map_d f := by rw [F.map_d, G.map_d]
  map_id X := by rw [F.map_id, G.map_id]
  map_comp g f := by rw [F.map_comp, G.map_comp]

/-- A composite DG functor acts on objects by the composite of its object maps. -/
@[simp, stacks 09L6 "composition of DG functors on objects"]
theorem comp_obj (G : DgFunctor R B C) (F : DgFunctor R A B) (X : A) :
    (G.comp F).obj X = G.obj (F.obj X) := rfl

/-- A composite DG functor acts on homogeneous morphisms by successive maps. -/
@[simp, stacks 09L6 "composition of DG functors on homogeneous morphisms"]
theorem comp_map (G : DgFunctor R B C) (F : DgFunctor R A B)
    {X Y : A} {n : ℤ} (f : X ⟶[n] Y) :
    (G.comp F).map f = G.map (F.map f) := rfl

/-- The linear map on a homogeneous Hom group of a composite DG functor is the composite of the
two degreewise linear maps. -/
@[simp, stacks 09L6 "composition of DG functors on homogeneous linear maps"]
theorem comp_mapLinear (G : DgFunctor R B C) (F : DgFunctor R A B)
    {X Y : A} (n : ℤ) :
    (G.comp F).mapLinear n =
      (G.mapLinear (X := F.obj X) (Y := F.obj Y) n).comp (F.mapLinear n) := rfl

/-- Left composition with the identity DG functor is strictly the original DG functor. -/
@[stacks 09L6 "left identity for DG functor composition"]
theorem id_comp (F : DgFunctor R A B) : (id R B).comp F = F := rfl

/-- Right composition with the identity DG functor is strictly the original DG functor. -/
@[stacks 09L6 "right identity for DG functor composition"]
theorem comp_id (F : DgFunctor R A B) : F.comp (id R A) = F := rfl

/-- DG functor composition is associative. -/
@[stacks 09L6 "associativity of DG functor composition"]
theorem comp_assoc (H : DgFunctor R C D) (G : DgFunctor R B C) (F : DgFunctor R A B) :
    H.comp (G.comp F) = (H.comp G).comp F := rfl

end DgFunctor

end DifferentialGradedCategory
