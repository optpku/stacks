/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Graded.Action

/-!
# Internally graded homogeneous submodules

This leaf records the additive and linear-algebraic fact that a homogeneous
submodule of an internally graded module inherits the ambient grading.  The
construction is stated over one base semiring; submodules originally defined
over a larger scalar ring use this API after `Submodule.restrictScalars`.
-/

@[expose] public section

open scoped DirectSum

noncomputable section

universe u v w uA uS

namespace DirectSum.Decomposition

variable {ι : Type u} [DecidableEq ι]
variable {R : Type v} [Semiring R]
variable {M : Type w} [AddCommMonoid M] [Module R M]

/-- The degree-`i` piece of a homogeneous submodule, represented as the comap of
the ambient degree piece along the subtype inclusion. -/
@[reducible, stacks 052N "homogeneous submodule grading family"]
def submoduleGrading
    (𝒜 : ι → Submodule R M) (P : Submodule R M) :
    ι → Submodule R P :=
  fun i ↦ (𝒜 i).comap P.subtype

namespace submoduleGrading

/-- Package the ambient homogeneous components of an element of a homogeneous
submodule as an element of its inherited direct sum. -/
@[stacks 052N "homogeneous submodule grading witness"]
noncomputable def witness
    (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (P : Submodule R M) (hP : SetLike.IsHomogeneous 𝒜 P) (x : P) :
    DirectSum ι (fun i ↦ ↥(submoduleGrading 𝒜 P i)) := by
  classical
  refine DFinsupp.mk (DirectSum.decompose 𝒜 (x : M)).support fun i ↦ ?_
  exact
    ⟨⟨((DirectSum.decompose 𝒜 (x : M) i.1 : 𝒜 i.1) : M), hP i.1 x.2⟩,
      (DirectSum.decompose 𝒜 (x : M) i.1).2⟩

/-- Recomposing the explicit inherited-grading witness recovers the original
submodule element. -/
@[stacks 052N "homogeneous submodule grading witness recomposition"]
theorem witness_recompose
    (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (P : Submodule R M) (hP : SetLike.IsHomogeneous 𝒜 P) (x : P) :
    DirectSum.coeAddMonoidHom (submoduleGrading 𝒜 P) (witness 𝒜 P hP x) = x := sorry

/-- Projecting the ambient recomposition of arbitrary inherited homogeneous pieces
reads off the corresponding submodule coordinate. -/
@[stacks 052N "homogeneous submodule ambient recomposition coordinate"]
theorem ambient_component_recompose
    (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (P : Submodule R M) (z : DirectSum ι (fun j ↦ ↥(submoduleGrading 𝒜 P j))) (i : ι) :
    ((DirectSum.decompose 𝒜
      ((DirectSum.coeAddMonoidHom (submoduleGrading 𝒜 P) z : P) : M) i : 𝒜 i) : M) =
        (((z i).1 : P) : M) := sorry

/-- The componentwise comaps of a homogeneous submodule form an internal direct
sum. -/
@[stacks 052N "homogeneous submodule internal decomposition"]
theorem isInternal
    (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (P : Submodule R M) (hP : SetLike.IsHomogeneous 𝒜 P) :
    DirectSum.IsInternal (submoduleGrading 𝒜 P) := sorry

/-- The direct-sum decomposition inherited by a homogeneous submodule.

This is a named construction rather than a global instance because the decomposition depends on
the supplied homogeneity witness.  Consumers install it locally only when they need the
definitional `DirectSum.decompose` interface. -/
@[reducible, stacks 052N "homogeneous submodule decomposition"]
noncomputable def decomposition
    (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (P : Submodule R M) (hP : SetLike.IsHomogeneous 𝒜 P) :
    DirectSum.Decomposition (submoduleGrading 𝒜 P) :=
  DirectSum.IsInternal.chooseDecomposition
    (submoduleGrading 𝒜 P) (isInternal 𝒜 P hP)

/-- The degree-`i` coordinate map for the inherited grading of a homogeneous
submodule.

The decomposition selected by `hP` stays internal to this construction.  Consumers can therefore
use a coordinate map without installing a proof-dependent `DirectSum.Decomposition` instance. -/
@[stacks 052N "homogeneous submodule component map"]
noncomputable def component
    (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (P : Submodule R M) (hP : SetLike.IsHomogeneous 𝒜 P) (i : ι) :
    P →ₗ[R] submoduleGrading 𝒜 P i := by
  letI : DirectSum.Decomposition (submoduleGrading 𝒜 P) := decomposition 𝒜 P hP
  exact
    (DirectSum.component R ι (fun j ↦ submoduleGrading 𝒜 P j) i).comp
      (DirectSum.decomposeLinearEquiv (submoduleGrading 𝒜 P)).toLinearMap

/-- After coercion to the ambient module, the inherited degree coordinate is the
corresponding coordinate of the ambient decomposition. -/
@[stacks 052N "homogeneous submodule component formula"]
theorem component_coe
    (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (P : Submodule R M) (hP : SetLike.IsHomogeneous 𝒜 P)
    {i : ι} (x : P) :
    (((component 𝒜 P hP i x : submoduleGrading 𝒜 P i) : P) : M) =
      ((DirectSum.decompose 𝒜 (x : M) i : 𝒜 i) : M) := sorry

/-- The decomposition coordinates of a homogeneous submodule are the explicit
ambient-component witness. -/
@[stacks 052N "homogeneous submodule decomposition witness formula"]
theorem decompose_eq_witness
    (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (P : Submodule R M) (hP : SetLike.IsHomogeneous 𝒜 P) (x : P) :
    letI : DirectSum.Decomposition (submoduleGrading 𝒜 P) := decomposition 𝒜 P hP
    DirectSum.decompose (submoduleGrading 𝒜 P) x = witness 𝒜 P hP x := sorry

/-- After coercion to the ambient module, an inherited homogeneous coordinate is
the corresponding coordinate of the ambient decomposition. -/
@[stacks 052N "homogeneous submodule ambient coordinate formula"]
theorem decompose_coe
    (𝒜 : ι → Submodule R M) [DirectSum.Decomposition 𝒜]
    (P : Submodule R M) (hP : SetLike.IsHomogeneous 𝒜 P)
    (x : P) (i : ι) :
    letI : DirectSum.Decomposition (submoduleGrading 𝒜 P) := decomposition 𝒜 P hP
    (((DirectSum.decompose (submoduleGrading 𝒜 P) x i).1 : P) : M) =
      ((DirectSum.decompose 𝒜 (x : M) i : 𝒜 i) : M) := sorry

variable {ιA : Type uA} [VAdd ιA ι]
variable {S : Type uS} [Semiring S] [Module R S]
variable [Module S M] [IsScalarTower R S M]

/-- The degreewise scalar action on a homogeneous submodule obtained by
restricting scalars to the base ring. -/
@[stacks 052N "homogeneous submodule graded scalar action membership"]
theorem smul_mem
    (𝒜 : ιA → Submodule R S) (ℳ : ι → Submodule R M) (P : Submodule S M)
    [SetLike.GradedSMul 𝒜 ℳ]
    {i : ιA} {j : ι} {a : S} {x : P.restrictScalars R}
    (ha : a ∈ 𝒜 i)
    (hx : x ∈ submoduleGrading ℳ (P.restrictScalars R) j) :
    a • x ∈ submoduleGrading ℳ (P.restrictScalars R) (i +ᵥ j) := sorry

/-- Package the inherited graded scalar action on a restricted-scalar submodule.

The construction is the canonical `Submodule.comapGradedSMul` along the subtype inclusion; no
other scalar or polynomial data is required. -/
@[reducible, stacks 052N "homogeneous submodule graded scalar action"]
def gradedSMul
    (𝒜 : ιA → Submodule R S) (ℳ : ι → Submodule R M) (P : Submodule S M)
    [SetLike.GradedSMul 𝒜 ℳ] :
    SetLike.GradedSMul 𝒜 (submoduleGrading ℳ (P.restrictScalars R)) where
  smul_mem := fun i j a x ha hx ↦ smul_mem 𝒜 ℳ P ha hx

end submoduleGrading

end DirectSum.Decomposition
