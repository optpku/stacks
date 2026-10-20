/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Graded.HomogeneousMap
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of translated homogeneous maps

This leaf specializes the degree-function API to additive degree translations.  It owns only the
transport needed to turn `(i + n) + m` into `i + (n + m)`; component, kernel, range, and quotient
constructions remain in their respective leaves.
-/

@[expose] public section

noncomputable section

universe i u v w x y z

namespace GradedModule.HomogeneousMap

variable {ι : Type i} [AddSemigroup ι]
variable {R : Type u} [Semiring R]
variable {M : Type x} [AddCommMonoid M] [Module R M]
variable {N : Type y} [AddCommMonoid N] [Module R N]
variable {P : Type z} [AddCommMonoid P] [Module R P]
variable {S : Type v} [Semiring S]
variable [Module S M] [Module S N] [SMulCommClass S R N]
variable [Module S P] [SMulCommClass S R P]

/-- Stacks `09MN`: the composite of two additive degree translations normalizes to their sum. -/
@[stacks 09MN "degree-translation composition normalization"]
theorem compDegree (n m : ι) :
    (fun i ↦ i + m) ∘ (fun i ↦ i + n) = fun i ↦ i + (n + m) := sorry

/-- Stacks `09MN`: the degree equality used to associate three additive translations. -/
@[stacks 09MN "degree-association transport"]
theorem assocDegree (n m l : ι) :
    (fun i ↦ i + ((n + m) + l)) = fun i ↦ i + (n + (m + l)) := sorry

/-- Stacks `09MN`: compose homogeneous maps whose degrees are additive translations. -/
@[stacks 09MN "composition of translated homogeneous maps"]
def comp
    {source : ι → Submodule R M} {middle : ι → Submodule R N}
    {target : ι → Submodule R P} {m n : ι}
    (g : GradedModule.HomogeneousMap S middle target m)
    (f : GradedModule.HomogeneousMap S source middle n) :
    GradedModule.HomogeneousMap S source target (n + m) :=
  GradedModule.MapsTo.castDegree (compDegree n m) (GradedModule.MapsTo.comp g f)

/-- Stacks `09MN`: the translated homogeneous composition has ordinary map composition as value. -/
@[simp, stacks 09MN "translated homogeneous composition computation"]
theorem comp_apply
    {source : ι → Submodule R M} {middle : ι → Submodule R N}
    {target : ι → Submodule R P} {m n : ι}
    (g : GradedModule.HomogeneousMap S middle target m)
    (f : GradedModule.HomogeneousMap S source middle n) (x : M) :
    GradedModule.MapsTo.toLinearMap (comp g f) x =
      GradedModule.MapsTo.toLinearMap g (GradedModule.MapsTo.toLinearMap f x) := sorry

/-- Stacks `09MN`: additive-translation composition is associative. -/
@[stacks 09MN "associativity of translated homogeneous composition"]
theorem comp_assoc
    {Q : Type w} [AddCommMonoid Q] [Module R Q] [Module S Q] [SMulCommClass S R Q]
    {source : ι → Submodule R M} {middle : ι → Submodule R N}
    {next : ι → Submodule R P} {target : ι → Submodule R Q}
    {l m n : ι}
    (h : GradedModule.HomogeneousMap S next target l)
    (g : GradedModule.HomogeneousMap S middle next m)
    (f : GradedModule.HomogeneousMap S source middle n) :
    GradedModule.MapsTo.castDegree (assocDegree n m l).symm (comp (comp h g) f) =
      comp h (comp g f) := sorry

end GradedModule.HomogeneousMap

namespace GradedModule.HomogeneousMap

variable {ι : Type i} [AddMonoid ι]
variable {R : Type u} [Semiring R]
variable {N : Type y} [AddCommMonoid N] [Module R N]
variable {S : Type v} [Semiring S] [Module S N] [SMulCommClass S R N]

/-- Stacks `09MN`: the identity degree function is translation by zero. -/
@[stacks 09MN "identity degree normalization"]
theorem idDegree :
    (fun i : ι ↦ i) = fun i ↦ i + 0 := sorry

/-- Stacks `09MN`: the identity linear map as a degree-zero homogeneous map. -/
@[stacks 09MN "degree-zero homogeneous identity map"]
def id {source : ι → Submodule R N} :
    GradedModule.HomogeneousMap S source source 0 :=
  GradedModule.MapsTo.castDegree idDegree (GradedModule.MapsTo.id (S := S) source)

/-- Stacks `09MN`: evaluation of the degree-zero homogeneous identity map. -/
@[simp, stacks 09MN "degree-zero homogeneous identity computation"]
theorem id_apply {source : ι → Submodule R N} (x : N) :
    GradedModule.MapsTo.toLinearMap (id (S := S) (source := source)) x = x := sorry

end GradedModule.HomogeneousMap

namespace GradedModule.HomogeneousMap

variable {ι : Type i} [AddMonoid ι]
variable {R : Type u} [Semiring R]
variable {M : Type x} [AddCommMonoid M] [Module R M]
variable {N : Type y} [AddCommMonoid N] [Module R N]
variable {P : Type z} [AddCommMonoid P] [Module R P]
variable {S : Type v} [Semiring S]
variable [Module S M] [Module S N] [SMulCommClass S R N]
variable [Module S P] [SMulCommClass S R P]

/-- Stacks `09MN`: right addition by zero does not change a translated degree function. -/
@[stacks 09MN "right-zero degree normalization"]
theorem addZeroDegree (n : ι) :
    (fun i ↦ i + (n + 0)) = fun i ↦ i + n := sorry

/-- Stacks `09MN`: left addition by zero does not change a translated degree function. -/
@[stacks 09MN "left-zero degree normalization"]
theorem zeroAddDegree (n : ι) :
    (fun i ↦ i + (0 + n)) = fun i ↦ i + n := sorry

/-- Stacks `09MN`: compose two degree-zero homogeneous maps without exposing `0 + 0` transport. -/
@[stacks 09MN "degree-zero homogeneous composition"]
def compZero
    {source : ι → Submodule R M} {middle : ι → Submodule R N}
    {target : ι → Submodule R P}
    (g : GradedModule.HomogeneousMap S middle target 0)
    (f : GradedModule.HomogeneousMap S source middle 0) :
    GradedModule.HomogeneousMap S source target 0 :=
  GradedModule.MapsTo.castDegree (addZeroDegree 0) (comp g f)

/-- Stacks `09MN`: degree-zero homogeneous composition has ordinary map composition as value. -/
@[simp, stacks 09MN "degree-zero homogeneous composition computation"]
theorem compZero_apply
    {source : ι → Submodule R M} {middle : ι → Submodule R N}
    {target : ι → Submodule R P}
    (g : GradedModule.HomogeneousMap S middle target 0)
    (f : GradedModule.HomogeneousMap S source middle 0) (x : M) :
    GradedModule.MapsTo.toLinearMap (compZero g f) x =
      GradedModule.MapsTo.toLinearMap g (GradedModule.MapsTo.toLinearMap f x) := sorry

/-- Stacks `09MN`: postcomposition by a degree-zero homogeneous map preserves the degree. -/
@[stacks 09MN "degree-zero postcomposition of a homogeneous map"]
def postcompZero
    {source : ι → Submodule R M} {middle : ι → Submodule R N}
    {target : ι → Submodule R P} {n : ι}
    (g : GradedModule.HomogeneousMap S middle target 0)
    (f : GradedModule.HomogeneousMap S source middle n) :
    GradedModule.HomogeneousMap S source target n :=
  GradedModule.MapsTo.castDegree (addZeroDegree n) (comp g f)

/-- Stacks `09MN`: degree-zero postcomposition has ordinary map composition as value. -/
@[simp, stacks 09MN "degree-zero postcomposition computation"]
theorem postcompZero_apply
    {source : ι → Submodule R M} {middle : ι → Submodule R N}
    {target : ι → Submodule R P} {n : ι}
    (g : GradedModule.HomogeneousMap S middle target 0)
    (f : GradedModule.HomogeneousMap S source middle n) (x : M) :
    GradedModule.MapsTo.toLinearMap (postcompZero g f) x =
      GradedModule.MapsTo.toLinearMap g (GradedModule.MapsTo.toLinearMap f x) := sorry

/-- Stacks `09MN`: precomposition by a degree-zero homogeneous map preserves the degree. -/
@[stacks 09MN "degree-zero precomposition of a homogeneous map"]
def precompZero
    {source : ι → Submodule R M} {middle : ι → Submodule R N}
    {target : ι → Submodule R P} {n : ι}
    (g : GradedModule.HomogeneousMap S middle target n)
    (f : GradedModule.HomogeneousMap S source middle 0) :
    GradedModule.HomogeneousMap S source target n :=
  GradedModule.MapsTo.castDegree (zeroAddDegree n) (comp g f)

/-- Stacks `09MN`: degree-zero precomposition has ordinary map composition as value. -/
@[simp, stacks 09MN "degree-zero precomposition computation"]
theorem precompZero_apply
    {source : ι → Submodule R M} {middle : ι → Submodule R N}
    {target : ι → Submodule R P} {n : ι}
    (g : GradedModule.HomogeneousMap S middle target n)
    (f : GradedModule.HomogeneousMap S source middle 0) (x : M) :
    GradedModule.MapsTo.toLinearMap (precompZero g f) x =
      GradedModule.MapsTo.toLinearMap g (GradedModule.MapsTo.toLinearMap f x) := sorry

/-- Postcomposition by the degree-zero identity leaves a homogeneous map unchanged. -/
@[simp, stacks 09MN "identity law for degree-zero postcomposition"]
theorem postcompZero_id
    {source : ι → Submodule R M} {target : ι → Submodule R N} {n : ι}
    (f : GradedModule.HomogeneousMap S source target n) :
    postcompZero (id (S := S) (source := target)) f = f := sorry

/-- Precomposition by the degree-zero identity leaves a homogeneous map unchanged. -/
@[simp, stacks 09MN "identity law for degree-zero precomposition"]
theorem precompZero_id [SMulCommClass S R M]
    {source : ι → Submodule R M} {target : ι → Submodule R N} {n : ι}
    (f : GradedModule.HomogeneousMap S source target n) :
    precompZero f (id (S := S) (source := source)) = f := sorry

/-- Degree-zero homogeneous composition is associative. -/
@[stacks 09MN "associativity of degree-zero homogeneous composition"]
theorem compZero_assoc
    {Q : Type w} [AddCommMonoid Q] [Module R Q] [Module S Q] [SMulCommClass S R Q]
    {source : ι → Submodule R M} {middle : ι → Submodule R N}
    {next : ι → Submodule R P} {target : ι → Submodule R Q}
    (h : GradedModule.HomogeneousMap S next target 0)
    (g : GradedModule.HomogeneousMap S middle next 0)
    (f : GradedModule.HomogeneousMap S source middle 0) :
    compZero (compZero h g) f = compZero h (compZero g f) := sorry

/-- Postcomposition by a fixed degree-zero map is linear on every homogeneous-map component. -/
@[stacks 09MN "linear degree-zero postcomposition"]
def postcompZeroLinear
    {source : ι → Submodule R M} {middle : ι → Submodule R N}
    {target : ι → Submodule R P} {n : ι}
    (g : GradedModule.HomogeneousMap S middle target 0) :
    GradedModule.HomogeneousMap S source middle n →ₗ[R]
      GradedModule.HomogeneousMap S source target n where
  toFun := postcompZero g
  map_add' := sorry
  map_smul' := sorry

/-- Precomposition by a fixed degree-zero map is linear on every homogeneous-map component. -/
@[stacks 09MN "linear degree-zero precomposition"]
def precompZeroLinear
    {source : ι → Submodule R M} {middle : ι → Submodule R N}
    {target : ι → Submodule R P} {n : ι}
    (f : GradedModule.HomogeneousMap S source middle 0) :
    GradedModule.HomogeneousMap S middle target n →ₗ[R]
      GradedModule.HomogeneousMap S source target n where
  toFun := fun g ↦ precompZero g f
  map_add' := sorry
  map_smul' := sorry

end GradedModule.HomogeneousMap

end
