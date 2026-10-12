/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Graded.HomogeneousMap
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Tactic.CrossRefAttribute

/-!
# Component maps of homogeneous maps

This leaf exposes the data-level operations needed by graded-map consumers.  A homogeneous map can
be restricted to one source component, scalar multiplication by a homogeneous element can be
packaged as a homogeneous endomorphism, and an endomorphism can be iterated together with its
degree function.  The constructions are independent of polynomial rings, quotient gradings, and
Noetherian hypotheses.

The component map is kept separate from projection theorems: it is a concrete linear map, while
membership, computation, and power-compatibility laws are Prop-valued companions.  This lets
downstream code build kernels, ranges, and rank-nullity statements from one shared data owner.
-/

@[expose] public section

universe i j w u v x y p

namespace GradedModule.MapsTo

variable {ι : Type i} {κ : Type j}
variable {R : Type u} [Semiring R]
variable {M : Type x} [AddCommMonoid M] [Module R M]
variable {N : Type y} [AddCommMonoid N] [Module R N]
variable {S : Type v} [Semiring S]
variable [Module S M] [Module S N] [SMulCommClass S R N]

/-- Stacks `09MN`: restrict a homogeneous map to one source component and its degree-selected target
component.

The scalar-change compatibility is required only here, where the map is viewed as `R`-linear;
the root `MapsTo` predicate itself remains independent of this extra bridge. -/
@[stacks 09MN "homogeneous map component linear map"]
def componentMap
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : GradedModule.MapsTo S source target degree)
    [LinearMap.CompatibleSMul M N R S] (i : ι) :
    source i →ₗ[R] target (degree i) :=
  LinearMap.codRestrict (target (degree i))
    ((LinearMap.restrictScalars R (GradedModule.MapsTo.toLinearMap f)).domRestrict (source i))
    (fun x ↦ map_mem f x.2)

/-- Stacks `09MN`: the component map has the same underlying value as the original homogeneous map. -/
@[simp, stacks 09MN "homogeneous map component computation"]
theorem componentMap_coe
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : GradedModule.MapsTo S source target degree)
    [LinearMap.CompatibleSMul M N R S] (i : ι) (x : source i) :
    ((componentMap f i x : target (degree i)) : N) =
      GradedModule.MapsTo.toLinearMap f (x : M) := sorry

/-- Stacks `09MN`: reindex a component map along an equality of grading indices. -/
@[stacks 09MN "homogeneous map component index transport"]
def componentMapOfEq
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : GradedModule.MapsTo S source target degree)
    [LinearMap.CompatibleSMul M N R S] (i : ι) {j : κ} (h : degree i = j) :
    source i →ₗ[R] target j :=
  h ▸ componentMap f i

/-- Stacks `09MN`: the reindexed component map keeps the same ambient value. -/
@[simp, stacks 09MN "reindexed homogeneous map component computation"]
theorem componentMapOfEq_coe
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree : ι → κ} (f : GradedModule.MapsTo S source target degree)
    [LinearMap.CompatibleSMul M N R S] (i : ι) {j : κ} (h : degree i = j)
    (x : source i) :
    ((componentMapOfEq f i h x : target j) : N) =
      GradedModule.MapsTo.toLinearMap f (x : M) := sorry

/-- Stacks `09MN`: restricting a degree-transported map agrees with transporting its component
map to the pointwise-equal target index. -/
@[stacks 09MN "component map compatibility with degree transport"]
theorem componentMap_castDegree
    {source : ι → Submodule R M} {target : κ → Submodule R N}
    {degree degree' : ι → κ} (h : degree = degree')
    (f : GradedModule.MapsTo S source target degree)
    [LinearMap.CompatibleSMul M N R S] (i : ι) :
    componentMap (GradedModule.MapsTo.castDegree h f) i =
      componentMapOfEq f i (congrFun h i) := sorry

section Composition

variable {ν : Type w} {P : Type p} [AddCommMonoid P] [Module R P]
variable [Module S P] [SMulCommClass S R P]

/-- Stacks `09MN`: component restriction commutes with composition of degree-following maps. -/
@[stacks 09MN "component map composition"]
theorem componentMap_comp
    {source : ι → Submodule R M} {middle : κ → Submodule R N}
    {target : ν → Submodule R P} {degree : ι → κ} {degree' : κ → ν}
    (g : GradedModule.MapsTo S middle target degree')
    (f : GradedModule.MapsTo S source middle degree)
    [LinearMap.CompatibleSMul M N R S] [LinearMap.CompatibleSMul N P R S]
    [LinearMap.CompatibleSMul M P R S] (i : ι) :
    componentMap (GradedModule.MapsTo.comp g f) i =
      (componentMap g (degree i)).comp (componentMap f i) := sorry

end Composition

/-- Stacks `09MN`: the component map of the degree-preserving identity is the identity map. -/
@[simp, stacks 09MN "component map identity"]
theorem componentMap_id
    {source : ι → Submodule R N} [LinearMap.CompatibleSMul N N R S] (i : ι) :
    componentMap (GradedModule.MapsTo.id (S := S) source) i = LinearMap.id := sorry

section Iterate

variable [SMulCommClass S R M]

/-- Stacks `09MN`: iterate a homogeneous endomorphism together with its degree function. -/
@[stacks 09MN "iterated homogeneous map"]
def pow
    {source : ι → Submodule R M} {degree : ι → ι}
    (f : GradedModule.MapsTo S source source degree) :
    (r : ℕ) → GradedModule.MapsTo S source source (degree^[r])
  | 0 => GradedModule.MapsTo.id (S := S) source
  | r + 1 => GradedModule.MapsTo.comp (pow f r) f

/-- Stacks `09MN`: the underlying linear map of an iterated homogeneous map is the ordinary
endomorphism power. -/
@[stacks 09MN "iterated homogeneous map underlying power"]
theorem coe_pow
    {source : ι → Submodule R M} {degree : ι → ι}
    (f : GradedModule.MapsTo S source source degree) (r : ℕ) :
    GradedModule.MapsTo.toLinearMap (pow f r) =
      GradedModule.MapsTo.toLinearMap f ^ r := sorry

/-- Stacks `09MN`: evaluation of an iterated homogeneous map agrees with the ordinary endomorphism
power. -/
@[simp, stacks 09MN "iterated homogeneous map power application"]
theorem pow_apply
    {source : ι → Submodule R M} {degree : ι → ι}
    (f : GradedModule.MapsTo S source source degree) (r : ℕ) (x : M) :
    GradedModule.MapsTo.toLinearMap (pow f r) x =
      (GradedModule.MapsTo.toLinearMap f ^ r) x := sorry

/-- Stacks `09MN`: powers of an injective-degree homogeneous endomorphism have homogeneous kernels.

The degree function is iterated together with the map, so callers do not have to rebuild the
induction or prove injectivity of every translated power at each use site. -/
@[stacks 09MN "homogeneous kernel of an iterated map"]
theorem ker_pow_isHomogeneous
    [DecidableEq ι]
    {source : ι → Submodule R M} {degree : ι → ι}
    (f : GradedModule.MapsTo S source source degree)
    [DirectSum.Decomposition source] (hdegree : Function.Injective degree) (r : ℕ) :
    DirectSum.SetLike.IsHomogeneous source
      (LinearMap.ker (GradedModule.MapsTo.toLinearMap (pow f r))) := sorry

/-- Stacks `09MN`: powers of an injective-degree homogeneous endomorphism have homogeneous
kernels after changing the coefficient ring to `R`. -/
@[stacks 09MN "base-scalar homogeneous kernel of an iterated map"]
theorem ker_pow_isHomogeneous_restrictScalars
    [DecidableEq ι]
    {source : ι → Submodule R M} {degree : ι → ι}
    (f : GradedModule.MapsTo S source source degree)
    [DirectSum.Decomposition source] [LinearMap.CompatibleSMul M M R S]
    (hdegree : Function.Injective degree) (r : ℕ) :
    DirectSum.SetLike.IsHomogeneous source
      (LinearMap.ker (LinearMap.restrictScalars R
        (GradedModule.MapsTo.toLinearMap (pow f r)))) := sorry

omit [SMulCommClass S R M] in
/-- Stacks `09MN`: a plain homogeneous endomorphism has homogeneous power kernels.

This bridge keeps ordinary `LinearMap` consumers from packaging the same map as a `MapsTo` value
just to invoke the bundled power theorem. -/
@[stacks 09MN "homogeneous power kernel of a plain linear map"]
theorem ker_pow_isHomogeneous_of_linearMap
    [DecidableEq ι]
    {source : ι → Submodule R M} {degree : ι → ι}
    (f : M →ₗ[S] M)
    (hf : ∀ i, Set.MapsTo f (source i) (source (degree i)))
    [DirectSum.Decomposition source] (hdegree : Function.Injective degree) (r : ℕ) :
    DirectSum.SetLike.IsHomogeneous source (LinearMap.ker (f ^ r)) := sorry

omit [SMulCommClass S R M] in
/-- Stacks `09MN`: the plain power-kernel bridge after changing coefficients to `R`. -/
@[stacks 09MN "base-scalar homogeneous power kernel of a plain linear map"]
theorem ker_pow_isHomogeneous_of_linearMap_restrictScalars
    [DecidableEq ι]
    {source : ι → Submodule R M} {degree : ι → ι}
    (f : M →ₗ[S] M)
    (hf : ∀ i, Set.MapsTo f (source i) (source (degree i)))
    [DirectSum.Decomposition source] [LinearMap.CompatibleSMul M M R S]
    (hdegree : Function.Injective degree) (r : ℕ) :
    DirectSum.SetLike.IsHomogeneous source
      (LinearMap.ker (LinearMap.restrictScalars R (f ^ r))) := sorry

end Iterate

end GradedModule.MapsTo

namespace GradedModule.MapsTo

universe a b r s m t z

variable {ιA : Type a} {ιM : Type b} [VAdd ιA ιM]
variable {R : Type r} [Semiring R]
variable {A : Type s}
variable {σ : Type z} [SetLike σ A]
variable {M : Type m} [AddCommMonoid M] [Module R M]
variable {T : Type t} [Semiring T] [Module T M]
variable [DistribSMul A M] [SMulCommClass A T M] [SMulCommClass T R M]

/-- Stacks `052N`: a bundled homogeneous scalar acts as a `T`-linear homogeneous endomorphism.

The component family remains an `R`-submodule family, while `T` is the ring over which the
underlying scalar-action map is linear.  Keeping these rings separate permits the same owner to
serve both base-linear component maps and the acting-ring kernel used by power arguments.
-/
@[stacks 052N "homogeneous scalar homogeneous map"]
def smul
    (𝒜 : ιA → σ) (ℳ : ιM → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ]
  {i : ιA} (a : 𝒜 i) :
    GradedModule.MapsTo T ℳ ℳ (fun j ↦ i +ᵥ j) :=
  ⟨DistribSMul.toLinearMap T M (a : A), sorry⟩

/-- Stacks `052N`: the homogeneous scalar map evaluates as the original scalar action. -/
@[simp, stacks 052N "homogeneous scalar map application"]
theorem smul_apply
    (𝒜 : ιA → σ) (ℳ : ιM → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ]
    {i : ιA} (a : 𝒜 i) (x : M) :
    (smul (T := T) 𝒜 ℳ a : M →ₗ[T] M) x = (a : A) • x := sorry

/-- Stacks `052N`: the scalar-action map is the corresponding scalar multiple of the identity
endomorphism.  This is the named equality bridge used by power and kernel consumers. -/
@[stacks 052N "homogeneous scalar map identity-endomorphism bridge"]
theorem smul_toLinearMap_eq_smul_id
    (𝒜 : ιA → σ) (ℳ : ιM → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ]
    [SMulCommClass T A M] {i : ιA} (a : 𝒜 i) :
    GradedModule.MapsTo.toLinearMap (smul (T := T) 𝒜 ℳ a) =
      (a : A) • (LinearMap.id : M →ₗ[T] M) := sorry

end GradedModule.MapsTo
