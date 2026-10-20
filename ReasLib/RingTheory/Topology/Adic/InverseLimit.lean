module

public import Mathlib.Algebra.GradedMulAction
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import ReasLib.Algebra.Category.ModuleCat.Topology.Limit
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic
public import ReasLib.RingTheory.Ideal.Filtration.AssociatedGraded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adic topologies from sequential module inverse systems

For a sequential inverse system `F`, the filtration used in limit-topology arguments has
`F⁰ = ⊤` and `Fⁿ⁺¹ = ker(lim F ⟶ Fₙ)`. This indexing matches the standard associated-graded
argument and keeps the topology, filtration, and ideal compatibility as separate reusable layers.
-/

@[expose] public section

open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u v w

namespace CategoryTheory.SequentialInverseSystem

variable {A : Type u} [CommRing A]

/-- The decreasing filtration on a sequential inverse limit with degree zero equal to the whole
limit and degree `n + 1` equal to the kernel of the projection to stage `n`. -/
@[stacks 0GYM "kernel filtration defining the limit topology"]
def limitFiltration (F : SequentialInverseSystem (ModuleCat.{v} A)) (n : ℕ) :
    Submodule A (limit F : ModuleCat.{v} A) :=
  match n with
  | 0 => ⊤
  | n + 1 => Functor.limitKernel F (Opposite.op n)

/-- Degree zero of the limit filtration is the whole inverse limit. -/
@[simp]
theorem limitFiltration_zero (F : SequentialInverseSystem (ModuleCat.{v} A)) :
    F.limitFiltration 0 = ⊤ := sorry

/-- The successor degree of the limit filtration is the corresponding projection kernel. -/
@[simp]
theorem limitFiltration_succ (F : SequentialInverseSystem (ModuleCat.{v} A)) (n : ℕ) :
    F.limitFiltration (n + 1) = Functor.limitKernel F (Opposite.op n) := sorry

/-- The limit filtration is decreasing. -/
theorem limitFiltration_succ_le
    (F : SequentialInverseSystem (ModuleCat.{v} A)) (n : ℕ) :
    F.limitFiltration (n + 1) ≤ F.limitFiltration n := sorry

/-- An ideal is compatible with the limit filtration when multiplication raises filtration
degree by one. -/
@[stacks 0GYM "ideal compatibility of the inverse-limit filtration"]
def IsIdealCompatible
    (F : SequentialInverseSystem (ModuleCat.{v} A)) (I : Ideal A) : Prop :=
  ∀ n : ℕ, I • F.limitFiltration n ≤ F.limitFiltration (n + 1)

/-- The limit filtration packaged as Mathlib's canonical `Ideal.Filtration`. -/
@[stacks 0GYM "ideal filtration on a sequential inverse limit"]
def idealFiltration
    (F : SequentialInverseSystem (ModuleCat.{v} A)) (I : Ideal A)
    (hI : F.IsIdealCompatible I) :
    I.Filtration (limit F : ModuleCat.{v} A) where
  N := F.limitFiltration
  mono := F.limitFiltration_succ_le
  smul_le := hI

/-- The underlying stages of the packaged ideal filtration are the limit-filtration stages. -/
@[simp]
theorem idealFiltration_N
    (F : SequentialInverseSystem (ModuleCat.{v} A)) (I : Ideal A)
    (hI : F.IsIdealCompatible I) (n : ℕ) :
    (F.idealFiltration I hI).N n = F.limitFiltration n := sorry

/-- Every transition presents stage `n` as the quotient of stage `n + 1` by
`I ^ (n + 1)`. -/
@[stacks 0GYM "successive ideal-power quotients in a module inverse system"]
def IsSuccessiveQuotient
    (F : SequentialInverseSystem (ModuleCat.{v} A)) (I : Ideal A) : Prop :=
  ∀ n : ℕ,
    LinearMap.ker (F.transitionMap (Nat.le_succ n)).hom =
        I ^ (n + 1) • (⊤ : Submodule A (F.obj (Opposite.op (n + 1)))) ∧
      Function.Surjective (F.transitionMap (Nat.le_succ n)).hom

namespace IsSuccessiveQuotient

variable {F : SequentialInverseSystem (ModuleCat.{v} A)} {I : Ideal A}

/-- The kernel clause of a successive ideal-power quotient system. -/
theorem kernel (h : F.IsSuccessiveQuotient I) (n : ℕ) :
    LinearMap.ker (F.transitionMap (Nat.le_succ n)).hom =
      I ^ (n + 1) • (⊤ : Submodule A (F.obj (Opposite.op (n + 1)))) := sorry

/-- The surjectivity clause of a successive ideal-power quotient system. -/
theorem surjective (h : F.IsSuccessiveQuotient I) (n : ℕ) :
    Function.Surjective
      (F.transitionMap (Nat.le_succ n)).hom := sorry

/-- Successive ideal-power quotients make the limit filtration ideal-compatible. -/
theorem isIdealCompatible (h : F.IsSuccessiveQuotient I) :
    F.IsIdealCompatible I := sorry

end IsSuccessiveQuotient

/-- Projection kernels, equivalently the positive-degree limit-filtration stages, form a basis of
neighborhoods of zero in the limit topology. -/
theorem limitNhds_zero_hasBasis_limitFiltration
    (F : SequentialInverseSystem (ModuleCat.{v} A)) :
    (Functor.limitNhds F 0).HasBasis
      (fun _ : ℕ ↦ True)
      (fun n ↦ (F.limitFiltration (n + 1) : Set (limit F : ModuleCat.{v} A))) := sorry

/-- A sequential inverse system has adic projection kernels from stage one when the kernel at
every positive stage `c` is `I ^ c` applied to the whole limit.  The name records that this is a
one-based projection statement, not the zero-based equation `limitFiltration n = I ^ n • ⊤`. -/
@[stacks 0EHA "ideal-power projection kernels on a sequential inverse limit"]
def HasAdicKernels
    (F : SequentialInverseSystem (ModuleCat.{v} A)) (I : Ideal A) : Prop :=
  ∀ c : ℕ, 1 ≤ c →
    Functor.limitKernel F (Opposite.op c) =
      I ^ c • (⊤ : Submodule A (limit F : ModuleCat.{v} A))

namespace HasAdicKernels

variable {F : SequentialInverseSystem (ModuleCat.{v} A)} {I : Ideal A}

/-- The projection-kernel computation supplied by an adic inverse limit. -/
theorem limitKernel (h : F.HasAdicKernels I) (c : ℕ) (hc : 1 ≤ c) :
    Functor.limitKernel F (Opposite.op c) =
      I ^ c • (⊤ : Submodule A (limit F : ModuleCat.{v} A)) := sorry

/-- Ideal-power projection kernels identify the limit topology with the adic topology. -/
@[stacks 0EHA "adic topology from ideal-power projection kernels"]
theorem limitTopology_eq_adic (h : F.HasAdicKernels I) :
    Functor.limitTopology F =
      Ideal.adicModuleTopology I (limit F : ModuleCat.{v} A) := sorry

end HasAdicKernels

/-- A Noetherian associated graded module for an ideal-compatible limit filtration identifies the
limit topology with the adic topology. -/
@[stacks 0GYM "Noetherian associated graded criterion for the limit topology"]
theorem limitTopology_eq_adic_of_isNoetherian
    (F : SequentialInverseSystem (ModuleCat.{v} A)) (I : Ideal A)
    (hI : F.IsIdealCompatible I)
    [IsNoetherian (Ideal.AssociatedGraded.ring I)
      (F.idealFiltration I hI).associatedGraded] :
    Functor.limitTopology F =
      Ideal.adicModuleTopology I (limit F : ModuleCat.{v} A) := sorry

/-- A surjective map from a Noetherian module onto the associated graded of an ideal-compatible
limit filtration is enough to identify the limit topology with the adic topology. -/
@[stacks 0GYM "surjective Noetherian source criterion for an inverse-limit topology"]
theorem limitTopology_eq_adic_of_surjective
    (F : SequentialInverseSystem (ModuleCat.{v} A)) (I : Ideal A)
    (hI : F.IsIdealCompatible I)
    {N : Type w} [AddCommGroup N] [Module (Ideal.AssociatedGraded.ring I) N]
    [IsNoetherian (Ideal.AssociatedGraded.ring I) N]
    (f : N →ₗ[Ideal.AssociatedGraded.ring I]
      (F.idealFiltration I hI).associatedGraded)
    (hf : Function.Surjective f) :
    Functor.limitTopology F =
      Ideal.adicModuleTopology I (limit F : ModuleCat.{v} A) := sorry

end CategoryTheory.SequentialInverseSystem
