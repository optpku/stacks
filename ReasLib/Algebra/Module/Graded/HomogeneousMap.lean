/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homogeneous Linear Maps

This leaf owns the grading-level notion of a linear map following a degree function.  Homogeneous
maps are the specialization to degree translation, and neither notion requires the carriers to be
packaged as objects of a particular graded-module category.
-/

@[expose] public section

noncomputable section

namespace GradedModule

universe i j l q u v w x y z

variable {ι : Type i} {κ : Type j} {ν : Type l} {μ : Type q}
variable {R : Type u} [Semiring R]
variable {M : Type x} [AddCommMonoid M] [Module R M]
variable {N : Type y} [AddCommMonoid N] [Module R N]

/-- The `R`-submodule of `S`-linear maps which send each source component into the target component
selected by `degree`. -/
@[stacks 09MN "linear maps following a map of grading indices"]
def MapsTo (S : Type v) [Semiring S] [Module S M] [Module S N] [SMulCommClass S R N]
    (source : ι → Submodule R M)
    (target : κ → Submodule R N) (degree : ι → κ) :
    Submodule R (M →ₗ[S] N) where
  carrier := {f | ∀ i (x : M), x ∈ source i → f x ∈ target (degree i)}
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

/-- Membership in `MapsTo source target degree` is its componentwise mapping condition. -/
@[stacks 09MN "degree-following map membership characterization"]
theorem mem_mapsTo_iff {S : Type v} [Semiring S] [Module S M] [Module S N]
    [SMulCommClass S R N] (source : ι → Submodule R M) (target : κ → Submodule R N)
    (degree : ι → κ) (f : M →ₗ[S] N) :
    f ∈ MapsTo S source target degree ↔
      ∀ i, Set.MapsTo f (source i) (target (degree i)) := sorry

/-- The `R`-submodule of `S`-linear maps which shift every grading index by the fixed degree `k`. -/
@[stacks 09MN "homogeneous linear maps between graded modules"]
abbrev HomogeneousMap [Add ι] (S : Type v) [Semiring S] [Module S M] [Module S N]
    [SMulCommClass S R N] (source : ι → Submodule R M)
    (target : ι → Submodule R N) (k : ι) : Submodule R (M →ₗ[S] N) :=
  MapsTo S source target (fun i ↦ i + k)

/-- Membership in `HomogeneousMap source target k` is the degree-shift condition on homogeneous
elements. -/
@[stacks 09MN "homogeneous map membership characterization"]
theorem mem_homogeneousMap_iff [Add ι] {S : Type v} [Semiring S]
    [Module S M] [Module S N] [SMulCommClass S R N] (source : ι → Submodule R M)
    (target : ι → Submodule R N) (k : ι) (f : M →ₗ[S] N) :
    f ∈ HomogeneousMap S source target k ↔
      ∀ i (x : M), x ∈ source i → f x ∈ target (i + k) := sorry

namespace MapsTo

variable {S : Type v} [Semiring S]
variable [Module S M] [Module S N] [SMulCommClass S R N]
variable {P : Type z} [AddCommMonoid P] [Module R P] [Module S P]
variable [SMulCommClass S R P]

/-- The underlying `S`-linear map of a degree-following map.

This named projection is the public boundary for the subtype carrier; consumers should use it
instead of depending on the implementation projection `.1`. -/
@[stacks 09MN "underlying linear map of a degree-following map"]
abbrev toLinearMap
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : GradedModule.MapsTo S source target degree) : M →ₗ[S] N := f.1

/-- Two degree-following maps with the same underlying linear map are equal. -/
@[ext, stacks 09MN "extensionality for degree-following maps"]
theorem ext
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} {f g : GradedModule.MapsTo S source target degree}
    (h : MapsTo.toLinearMap f = MapsTo.toLinearMap g) : f = g := sorry

/-- Membership in a degree-following map is the ordinary `Set.MapsTo` condition on one source
component. -/
@[stacks 09MN "homogeneous map component membership"]
theorem map_mem
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : GradedModule.MapsTo S source target degree)
    {i : ι} {x : M} (hx : x ∈ source i) :
    MapsTo.toLinearMap f x ∈ target (degree i) := sorry

/-- Composition of maps following degree functions follows the composite degree function. -/
@[stacks 09MN "composition of degree-following maps"]
def comp {source : ι → Submodule R M} {middle : κ → Submodule R N}
    {target : ν → Submodule R P} {degree : ι → κ} {degree' : κ → ν}
    (g : GradedModule.MapsTo S middle target degree')
    (f : GradedModule.MapsTo S source middle degree) :
    GradedModule.MapsTo S source target (degree' ∘ degree) :=
  ⟨(MapsTo.toLinearMap g).comp (MapsTo.toLinearMap f), sorry⟩

/-- Composition in `MapsTo` is ordinary composition on underlying linear maps. -/
@[simp, stacks 09MN "composition computation for degree-following maps"]
theorem comp_apply {source : ι → Submodule R M} {middle : κ → Submodule R N}
    {target : ν → Submodule R P} {degree : ι → κ} {degree' : κ → ν}
    (g : GradedModule.MapsTo S middle target degree')
    (f : GradedModule.MapsTo S source middle degree) (x : M) :
    MapsTo.toLinearMap (MapsTo.comp g f) x = MapsTo.toLinearMap g (MapsTo.toLinearMap f x) := sorry

/-- The identity linear map follows the identity degree function. -/
@[stacks 09MN "identity degree-following map"]
def id {S : Type v} [Semiring S] [Module S N] [SMulCommClass S R N]
    (source : ι → Submodule R N) :
    GradedModule.MapsTo S source source (fun i ↦ i) :=
  ⟨LinearMap.id, sorry⟩

/-- The identity in `MapsTo` acts as the identity on the underlying carrier. -/
@[simp, stacks 09MN "identity computation for degree-following maps"]
theorem id_apply {S : Type v} [Semiring S] [Module S N] [SMulCommClass S R N]
    (source : ι → Submodule R N) (x : N) :
    MapsTo.toLinearMap (MapsTo.id (S := S) source) x = x := sorry

/-- Composition on the right by the degree-function identity does not change a degree-following
map. -/
@[simp, stacks 09MN "right identity for degree-following map composition"]
theorem comp_id [SMulCommClass S R M]
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : GradedModule.MapsTo S source target degree) :
    MapsTo.comp f (MapsTo.id (S := S) source) = f := sorry

/-- Composition on the left by the degree-function identity does not change a degree-following
map. -/
@[simp, stacks 09MN "left identity for degree-following map composition"]
theorem id_comp
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : GradedModule.MapsTo S source target degree) :
    MapsTo.comp (MapsTo.id (S := S) target) f = f := sorry

/-- Composition of degree-following maps is associative. -/
@[stacks 09MN "associativity of degree-following map composition"]
theorem comp_assoc
    {Q : Type w} [AddCommMonoid Q] [Module R Q] [Module S Q] [SMulCommClass S R Q]
    {source : ι → Submodule R M} {middle : κ → Submodule R N}
    {next : ν → Submodule R P} {target : μ → Submodule R Q}
    {degree : ι → κ} {degree' : κ → ν} {degree'' : ν → μ}
    (h : GradedModule.MapsTo S next target degree'')
    (g : GradedModule.MapsTo S middle next degree')
    (f : GradedModule.MapsTo S source middle degree) :
    MapsTo.comp (MapsTo.comp h g) f = MapsTo.comp h (MapsTo.comp g f) := sorry

/-- Transport a degree-following map along an equality of degree functions. -/
@[stacks 09MN "degree-function transport for degree-following maps"]
def castDegree
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree degree' : ι → κ} (h : degree = degree')
    (f : GradedModule.MapsTo S source target degree) :
    GradedModule.MapsTo S source target degree' := h ▸ f

/-- Degree-function transport does not change the underlying linear map. -/
@[simp, stacks 09MN "degree-function transport computation"]
theorem castDegree_apply
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree degree' : ι → κ} (h : degree = degree')
    (f : GradedModule.MapsTo S source target degree) (x : M) :
    MapsTo.toLinearMap (castDegree h f) x = MapsTo.toLinearMap f x := sorry

/-- A homogeneous input is recovered by the matching target projection. -/
@[stacks 09MN "matching projection of a homogeneous map"]
theorem decompose_apply_of_mem
    [DecidableEq κ]
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : GradedModule.MapsTo S source target degree)
    [DirectSum.Decomposition target] {i : ι} {x : M} (hx : x ∈ source i) :
    (DirectSum.decompose target (MapsTo.toLinearMap f x) (degree i) : N) =
      MapsTo.toLinearMap f x := sorry

/-- A homogeneous input has zero target projection away from its image degree. -/
@[stacks 09MN "off-degree projection of a homogeneous map"]
theorem decompose_apply_of_ne
    [DecidableEq κ]
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : GradedModule.MapsTo S source target degree)
    [DirectSum.Decomposition target] {i : ι} {j : κ} {x : M} (hx : x ∈ source i)
    (hij : degree i ≠ j) :
    (DirectSum.decompose target (MapsTo.toLinearMap f x) j : N) = 0 := sorry

/-
API design: `DirectSum.SetLike.IsHomogeneous` observes only carriers, so the primary kernel/range
owners stay over the map's acting ring `S`.  A base-ring `restrictScalars` companion is supplied only
at the boundary where a downstream theorem genuinely needs `Submodule R`.  Injectivity is needed for
kernels, because different source components can otherwise cancel; it is not needed for ranges,
whose target projection is the image of the sum of all matching source components.
-/

/-- A degree-following map commutes with the matching projection when its degree function is
injective.  This bundled form is the shared projection infrastructure for kernel and component
calculations. -/
@[stacks 09MN "injective-degree projection commutation"]
theorem decompose_apply_eq
    [DecidableEq ι] [DecidableEq κ]
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : GradedModule.MapsTo S source target degree)
    [DirectSum.Decomposition source] [DirectSum.Decomposition target]
    (hdegree : Function.Injective degree) (y : M) (i : ι) :
    (DirectSum.decompose target (MapsTo.toLinearMap f y) (degree i) : N) =
      MapsTo.toLinearMap f (DirectSum.decompose source y i : M) := sorry

/-- The kernel of an injective-degree homogeneous map is homogeneous in the source. -/
@[stacks 09MN "kernel of an injective-degree homogeneous map"]
theorem ker_isHomogeneous
    [DecidableEq ι] [DecidableEq κ]
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : GradedModule.MapsTo S source target degree)
    [DirectSum.Decomposition source] [DirectSum.Decomposition target]
    (hdegree : Function.Injective degree) :
    DirectSum.SetLike.IsHomogeneous source
      (LinearMap.ker (MapsTo.toLinearMap f)) := sorry

/-- The base-scalar kernel companion for consumers that compute over `R`. -/
@[stacks 09MN "base-scalar kernel of an injective-degree homogeneous map"]
theorem ker_isHomogeneous_restrictScalars
    [DecidableEq ι] [DecidableEq κ]
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : GradedModule.MapsTo S source target degree)
    [DirectSum.Decomposition source] [DirectSum.Decomposition target]
    [LinearMap.CompatibleSMul M N R S] (hdegree : Function.Injective degree) :
    DirectSum.SetLike.IsHomogeneous source
      (LinearMap.ker (LinearMap.restrictScalars R (MapsTo.toLinearMap f))) := sorry

/-- The range of a degree-following map is homogeneous in the target.  No degree injectivity is
needed: all source components in one target fibre remain in the range. -/
@[stacks 09MN "range of a degree-following homogeneous map"]
theorem range_isHomogeneous
    [DecidableEq ι] [DecidableEq κ]
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : GradedModule.MapsTo S source target degree)
    [DirectSum.Decomposition source] [DirectSum.Decomposition target]
    :
    DirectSum.SetLike.IsHomogeneous target
      (LinearMap.range (MapsTo.toLinearMap f)) := sorry

/-- The base-scalar range companion for consumers that compute over `R`. -/
@[stacks 09MN "base-scalar range of a homogeneous map"]
theorem range_isHomogeneous_restrictScalars
    [DecidableEq ι] [DecidableEq κ]
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : GradedModule.MapsTo S source target degree)
    [DirectSum.Decomposition source] [DirectSum.Decomposition target]
    [LinearMap.CompatibleSMul M N R S] :
    DirectSum.SetLike.IsHomogeneous target
      (LinearMap.range (LinearMap.restrictScalars R (MapsTo.toLinearMap f))) := sorry

omit [SMulCommClass S R N] in
/-- The range of a plain `S`-linear map is homogeneous when it maps each source component to the
corresponding target component. -/
@[stacks 09MN "range of a plain homogeneous linear map"]
theorem range_isHomogeneous_of_linearMap
    [DecidableEq ι] [DecidableEq κ]
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : M →ₗ[S] N)
    (hf : ∀ i, Set.MapsTo f (source i) (target (degree i)))
    [DirectSum.Decomposition source] [DirectSum.Decomposition target]
    :
    DirectSum.SetLike.IsHomogeneous target (LinearMap.range f) := sorry

omit [SMulCommClass S R N] in
/-- The range of a plain homogeneous map remains homogeneous after changing coefficients to `R`. -/
@[stacks 09MN "base-scalar range of a plain homogeneous linear map"]
theorem range_isHomogeneous_of_linearMap_restrictScalars
    [DecidableEq ι] [DecidableEq κ]
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : M →ₗ[S] N)
    (hf : ∀ i, Set.MapsTo f (source i) (target (degree i)))
    [DirectSum.Decomposition source] [DirectSum.Decomposition target]
    [LinearMap.CompatibleSMul M N R S] :
    DirectSum.SetLike.IsHomogeneous target
      (LinearMap.range (LinearMap.restrictScalars R f)) := sorry

omit [SMulCommClass S R N] in
/-- The kernel of a plain `S`-linear map is homogeneous when its component map has injective degree
function. -/
@[stacks 09MN "kernel of a plain homogeneous linear map"]
theorem ker_isHomogeneous_of_linearMap
    [DecidableEq ι] [DecidableEq κ]
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : M →ₗ[S] N)
    (hf : ∀ i, Set.MapsTo f (source i) (target (degree i)))
    [DirectSum.Decomposition source] [DirectSum.Decomposition target]
    (hdegree : Function.Injective degree) :
    DirectSum.SetLike.IsHomogeneous source (LinearMap.ker f) := sorry

omit [SMulCommClass S R N] in
/-- The kernel of a plain homogeneous map remains homogeneous after changing coefficients to `R`. -/
@[stacks 09MN "base-scalar kernel of a plain homogeneous linear map"]
theorem ker_isHomogeneous_of_linearMap_restrictScalars
    [DecidableEq ι] [DecidableEq κ]
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : M →ₗ[S] N)
    (hf : ∀ i, Set.MapsTo f (source i) (target (degree i)))
    [DirectSum.Decomposition source] [DirectSum.Decomposition target]
    [LinearMap.CompatibleSMul M N R S] (hdegree : Function.Injective degree) :
    DirectSum.SetLike.IsHomogeneous source
      (LinearMap.ker (LinearMap.restrictScalars R f)) := sorry

omit [SMulCommClass S R N] in
/-- A degree-preserving linear map commutes with the matching homogeneous projections. -/
@[stacks 09MN "matching projection of a plain homogeneous linear map"]
theorem decompose_apply_eq_of_linearMap
    [DecidableEq ι]
    {source : ι → Submodule R M} {target : ι → Submodule R N}
    (f : M →ₗ[S] N)
    (hf : ∀ i, Set.MapsTo f (source i) (target i))
    [DirectSum.Decomposition source] [DirectSum.Decomposition target]
    (y : M) (i : ι) :
    ((DirectSum.decompose target (f y) i : target i) : N) =
      f ((DirectSum.decompose source y i : source i) : M) := sorry

end MapsTo

end GradedModule
