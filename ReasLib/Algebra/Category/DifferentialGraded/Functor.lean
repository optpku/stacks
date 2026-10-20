/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded

/-!
# Differential Graded Functors

This leaf owns the enrichment-level notion of a functor between differential graded categories
and its degreewise linearity API. It intentionally does not construct functors on closed
morphisms or on homotopy categories.
-/

@[expose] public section

universe u v w

namespace DifferentialGradedCategory

open scoped DifferentialGradedCategory

/-- Definition 22.26.2: a functor of differential graded categories over `R`. It consists of an
object map and graded `R`-linear maps on morphism groups, compatible with the differential,
identities, and graded composition. -/
@[stacks 09L6]
structure DgFunctor (R : Type u) [CommRing R] (A : Type v) (B : Type w)
    [DA : DifferentialGradedCategory R A] [DB : DifferentialGradedCategory R B] where
  /-- The action on objects. -/
  obj : A → B
  /-- The action on degree-`n` homogeneous morphisms. -/
  map {X Y : A} {n : ℤ} : (X ⟶[n] Y) → (obj X) ⟶[n] (obj Y)
  /-- The action on morphisms is additive. -/
  map_add {X Y : A} {n : ℤ} (f g : X ⟶[n] Y) : map (f + g) = map f + map g
  /-- The action on morphisms is `R`-linear. -/
  map_smul {X Y : A} {n : ℤ} (r : R) (f : X ⟶[n] Y) : map (r • f) = r • map f
  /-- The action commutes with differentials. -/
  map_d {X Y : A} {n : ℤ} (f : X ⟶[n] Y) : map (DA.d n f) = DB.d n (map f)
  /-- The action preserves identities. -/
  map_id (X : A) : map (DA.id X) = DB.id (obj X)
  /-- The action preserves graded composition. -/
  map_comp {X Y Z : A} {i j : ℤ} (g : Y ⟶[j] Z) (f : X ⟶[i] Y) :
    map (DA.comp g f) = DB.comp (map g) (map f)

namespace DgFunctor

variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w}
variable [DA : DifferentialGradedCategory R A] [DB : DifferentialGradedCategory R B]

attribute [simp] DgFunctor.map_add DgFunctor.map_smul DgFunctor.map_d
  DgFunctor.map_id DgFunctor.map_comp

/-- The degree-`n` morphism map of a DG functor as an `R`-linear map. -/
@[stacks 09L6 "degreewise linear map of a DG functor"]
def mapLinear (F : DgFunctor R A B) {X Y : A} (n : ℤ) :
    (X ⟶[n] Y) →ₗ[R] ((F.obj X) ⟶[n] (F.obj Y)) where
  toFun := F.map
  map_add' := F.map_add
  map_smul' := F.map_smul

/-- Applying `mapLinear` is the degreewise action of the DG functor. -/
@[simp, stacks 09L6 "DG functor linear map evaluation"]
theorem mapLinear_apply (F : DgFunctor R A B) {X Y : A} (n : ℤ) (f : X ⟶[n] Y) :
    F.mapLinear n f = F.map f := sorry

/-- A DG functor sends zero homogeneous morphisms to zero. -/
theorem map_zero (F : DgFunctor R A B) {X Y : A} (n : ℤ) :
    F.map (0 : X ⟶[n] Y) = (0 : (F.obj X) ⟶[n] (F.obj Y)) := sorry

/-- A DG functor commutes with negation on homogeneous morphisms. -/
theorem map_neg (F : DgFunctor R A B) {X Y : A} (n : ℤ) (f : X ⟶[n] Y) :
    F.map (-f) = -F.map f := sorry

/-- A DG functor commutes with subtraction on homogeneous morphisms. -/
theorem map_sub (F : DgFunctor R A B) {X Y : A} (n : ℤ) (f g : X ⟶[n] Y) :
    F.map (f - g) = F.map f - F.map g := sorry

end DgFunctor

end DifferentialGradedCategory
