/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.DirectSum.Decomposition.Transport
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Algebra

/-!
# Universe lifts of internally graded algebras

This leaf transports an internal grading, its direct-sum decomposition, and
compatible graded-module actions along the canonical equivalence between a
type and its universe lift.  The construction is independent of a particular
presentation, quotient, or localization chart.

The homogeneous-away comparison is built from explicit upward and downward
maps.  Thus its computational data does not depend on a choice extracted
from a bijectivity proof.
-/

@[expose] public section

open scoped DirectSum
open HomogeneousLocalization

universe u v w x y

namespace ULift

section SubmoduleFamily

variable {R : Type u} [Semiring R]
variable {A : Type v} [AddCommMonoid A] [Module R A]
variable {ι : Type w}

/-- The family of submodules obtained by mapping each member of `𝒜` through
the canonical linear equivalence `A ≃ₗ[R] ULift A`. -/
@[stacks 052N "universe-lifted submodule family"]
def submoduleFamily (𝒜 : ι → Submodule R A) :
    ι → Submodule R (ULift.{x} A) :=
  fun i ↦ (𝒜 i).map
    (ULift.moduleEquiv : ULift.{x} A ≃ₗ[R] A).symm.toLinearMap

/-- Membership in a component of `ULift.submoduleFamily` is detected after
applying the canonical map `ULift.down`. -/
@[simp, stacks 052N "universe-lifted submodule membership"]
theorem mem_submoduleFamily_iff (𝒜 : ι → Submodule R A) (i : ι)
    (a : ULift.{x} A) :
    a ∈ submoduleFamily 𝒜 i ↔ a.down ∈ 𝒜 i := sorry

/-- The canonical linear map from an original homogeneous component to its
universe-lifted component. -/
@[stacks 052N "universe-lifted homogeneous component map"]
def componentMap (𝒜 : ι → Submodule R A) (i : ι) :
    𝒜 i →ₗ[R] submoduleFamily 𝒜 i :=
  LinearMap.codRestrict
    (submoduleFamily 𝒜 i)
    ((ULift.moduleEquiv : ULift.{x} A ≃ₗ[R] A).symm.toLinearMap.comp
      (𝒜 i).subtype)
    fun a ↦ (mem_submoduleFamily_iff 𝒜 i (ULift.up (a : A))).2 a.2

/-- The canonical linear map from a universe-lifted homogeneous component
back to the original component. -/
@[stacks 052N "universe-lifted homogeneous component down map"]
def componentDownMap (𝒜 : ι → Submodule R A) (i : ι) :
    submoduleFamily 𝒜 i →ₗ[R] 𝒜 i :=
  LinearMap.codRestrict
    (𝒜 i)
    ((ULift.moduleEquiv : ULift.{x} A ≃ₗ[R] A).toLinearMap.comp
      (submoduleFamily 𝒜 i).subtype)
    fun a ↦ (mem_submoduleFamily_iff 𝒜 i a.1).1 a.2

/-- The lifted component map is the canonical `ULift.up` map on underlying
elements. -/
@[simp, stacks 052N "universe-lifted homogeneous component map application"]
theorem coe_componentMap_apply (𝒜 : ι → Submodule R A) (i : ι) (a : 𝒜 i) :
    (componentMap 𝒜 i a : ULift.{x} A) = ULift.up (a : A) := sorry

/-- Regard an element of a homogeneous component as an element of the
corresponding component of the universe-lifted family. -/
@[stacks 052N "universe-lifted homogeneous element"]
def submoduleFamilyElement (𝒜 : ι → Submodule R A) {i : ι} (a : 𝒜 i) :
    submoduleFamily 𝒜 i :=
  componentMap 𝒜 i a

end SubmoduleFamily

section Decomposition

variable {R : Type u} [Semiring R]
variable {A : Type v} [AddCommMonoid A] [Module R A]
variable {ι : Type w} [DecidableEq ι]

/-- Transport an internal direct-sum decomposition through the canonical
linear equivalence from `A` to `ULift A`. -/
@[reducible, stacks 052N "universe-lifted direct-sum decomposition"]
noncomputable def decomposition (𝒜 : ι → Submodule R A)
    [DirectSum.Decomposition 𝒜] :
    DirectSum.Decomposition (submoduleFamily 𝒜) :=
  DirectSum.Decomposition.map 𝒜
    (ULift.moduleEquiv : ULift.{x} A ≃ₗ[R] A).symm

end Decomposition

section GradedAlgebra

variable {R : Type u} [CommSemiring R]
variable {A : Type v} [Semiring A] [Algebra R A]
variable {ι : Type w} [DecidableEq ι] [AddMonoid ι]

/-- The lifted unit belongs to degree zero of the transported family. -/
@[stacks 052N "universe-lifted graded unit"]
theorem one_mem_submoduleFamily (𝒜 : ι → Submodule R A)
    [SetLike.GradedMonoid 𝒜] :
    (1 : ULift.{x} A) ∈ submoduleFamily 𝒜 0 := sorry

/-- Products of elements in lifted homogeneous components have the expected
sum of degrees. -/
@[stacks 052N "universe-lifted graded multiplication"]
theorem mul_mem_submoduleFamily (𝒜 : ι → Submodule R A)
    [SetLike.GradedMonoid 𝒜] {i j : ι} {a b : ULift.{x} A}
    (ha : a ∈ submoduleFamily 𝒜 i) (hb : b ∈ submoduleFamily 𝒜 j) :
    a * b ∈ submoduleFamily 𝒜 (i + j) := sorry

/-- The multiplicative grading on the universe-lifted family. -/
@[reducible, stacks 052N "universe-lifted graded monoid"]
def gradedMonoid (𝒜 : ι → Submodule R A) [SetLike.GradedMonoid 𝒜] :
    SetLike.GradedMonoid (submoduleFamily 𝒜) where
  one_mem := one_mem_submoduleFamily 𝒜
  mul_mem := fun _ _ _ _ ha hb ↦ mul_mem_submoduleFamily 𝒜 ha hb

/-- The internal grading on the universe lift of a graded algebra. -/
@[reducible, stacks 052N "universe-lifted graded algebra"]
noncomputable def gradedAlgebra (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] :
    GradedAlgebra (submoduleFamily 𝒜) :=
  { gradedMonoid 𝒜,
    decomposition 𝒜 with }

/-- The canonical grading on `ULift A` induced by an internal grading on
`A`.  It is an instance because the transport is determined uniquely by the
canonical universe equivalence. -/
@[stacks 052N "universe-lifted graded algebra instance"]
noncomputable instance submoduleFamilyGradedAlgebra
    (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] :
    GradedAlgebra (submoduleFamily 𝒜) :=
  gradedAlgebra 𝒜

/-- The component maps are mutually inverse in degree zero. -/
@[stacks 052N "universe-lifted degree-zero component inverse"]
theorem componentMap_leftInverse (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] :
    Function.LeftInverse (componentDownMap 𝒜 0) (componentMap 𝒜 0) := sorry

/-- The component maps are mutually inverse in degree zero after lifting. -/
@[stacks 052N "universe-lifted degree-zero component right inverse"]
theorem componentMap_rightInverse (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] :
    Function.RightInverse (componentDownMap 𝒜 0) (componentMap 𝒜 0) := sorry

/-- The degree-zero component map preserves multiplication. -/
@[stacks 052N "universe-lifted degree-zero multiplication"]
theorem componentMap_map_mul (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    (a b : 𝒜 0) :
    componentMap 𝒜 0 (a * b) = componentMap 𝒜 0 a * componentMap 𝒜 0 b := sorry

/-- The degree-zero component map commutes with the base algebra map. -/
@[stacks 052N "universe-lifted degree-zero algebra map"]
theorem componentMap_commutes (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    (r : R) :
    componentMap 𝒜 0 (algebraMap R (𝒜 0) r) =
      algebraMap R (submoduleFamily 𝒜 0) r := sorry

/-- The canonical algebra equivalence between the degree-zero components of
a grading and its universe lift. -/
@[stacks 052N "universe-lifted degree-zero algebra equivalence"]
noncomputable def zeroAlgEquiv (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] :
    𝒜 0 ≃ₐ[R] submoduleFamily 𝒜 0 where
  toFun := componentMap 𝒜 0
  invFun := componentDownMap 𝒜 0
  left_inv := componentMap_leftInverse 𝒜
  right_inv := componentMap_rightInverse 𝒜
  map_mul' := componentMap_map_mul 𝒜
  map_add' := (componentMap 𝒜 0).map_add
  commutes' := componentMap_commutes 𝒜

end GradedAlgebra

section GradedModule

variable {R : Type u} [CommSemiring R]
variable {A : Type v} [Semiring A] [Algebra R A]
variable {M : Type w} [AddCommMonoid M] [Module R M] [Module A M]
variable {ι : Type*} [AddMonoid ι]

/-- Scalar multiplication of lifted homogeneous elements stays in the
lifted component with the sum of the two degrees. -/
@[stacks 052N "universe-lifted graded scalar multiplication"]
theorem smul_mem_submoduleFamily (𝒜 : ι → Submodule R A)
    (ℳ : ι → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ]
    {i j : ι} {a : ULift.{x} A} {m : ULift.{y} M}
    (ha : a ∈ submoduleFamily 𝒜 i) (hm : m ∈ submoduleFamily ℳ j) :
    a • m ∈ submoduleFamily ℳ (i + j) := sorry

/-- The graded scalar action on universe-lifted families. -/
@[reducible, stacks 052N "universe-lifted graded scalar action"]
def gradedSMul (𝒜 : ι → Submodule R A) (ℳ : ι → Submodule R M)
    [SetLike.GradedSMul 𝒜 ℳ] :
    SetLike.GradedSMul (submoduleFamily 𝒜) (submoduleFamily ℳ) where
  smul_mem := fun _ _ _ _ ha hm ↦ smul_mem_submoduleFamily 𝒜 ℳ ha hm

/-- A compatible graded action transports canonically to the universe-lifted
ring and module. -/
@[stacks 052N "universe-lifted graded scalar action instance"]
noncomputable instance submoduleFamilyGradedSMul
    (𝒜 : ι → Submodule R A) (ℳ : ι → Submodule R M)
    [SetLike.GradedSMul 𝒜 ℳ] :
    SetLike.GradedSMul (submoduleFamily 𝒜) (submoduleFamily ℳ) :=
  gradedSMul 𝒜 ℳ

end GradedModule

section GradedRingHom

variable {R : Type u} [CommSemiring R]
variable {A : Type v} [CommRing A] [Algebra R A]
variable {ι : Type w}

/-- The upward universe-lift ring map preserves each member of an arbitrary
submodule family. -/
@[stacks 052N "universe-lifted graded ring map"]
theorem upGradedRingHom_map_mem (𝒜 : ι → Submodule R A)
    {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    ULift.up a ∈ submoduleFamily 𝒜 i := sorry

/-- The canonical upward ring map viewed as a graded ring homomorphism. -/
@[stacks 052N "universe-lifted upward graded ring homomorphism"]
noncomputable def upGradedRingHom (𝒜 : ι → Submodule R A) :
    𝒜 →+*ᵍ submoduleFamily 𝒜 where
  __ := (ULift.ringEquiv : ULift.{x} A ≃+* A).symm.toRingHom
  map_mem := upGradedRingHom_map_mem 𝒜

/-- The downward universe-lift ring map preserves each member of the
transported submodule family. -/
@[stacks 052N "universe-lifted downward graded ring map"]
theorem downGradedRingHom_map_mem (𝒜 : ι → Submodule R A)
    {i : ι} {a : ULift.{x} A} (ha : a ∈ submoduleFamily 𝒜 i) :
    a.down ∈ 𝒜 i := sorry

/-- The canonical downward ring map viewed as a graded ring homomorphism. -/
@[stacks 052N "universe-lifted downward graded ring homomorphism"]
noncomputable def downGradedRingHom (𝒜 : ι → Submodule R A) :
    submoduleFamily 𝒜 →+*ᵍ 𝒜 where
  __ := (ULift.ringEquiv : ULift.{x} A ≃+* A).toRingHom
  map_mem := downGradedRingHom_map_mem 𝒜

/-- Projecting after the upward graded map is the identity. -/
@[stacks 052N "universe-lifted graded ring map left inverse"]
theorem down_comp_upGradedRingHom (𝒜 : ι → Submodule R A) :
    (downGradedRingHom 𝒜).comp (upGradedRingHom 𝒜) = GradedRingHom.id 𝒜 := sorry

/-- Lifting after the downward graded map is the identity. -/
@[stacks 052N "universe-lifted graded ring map right inverse"]
theorem up_comp_downGradedRingHom (𝒜 : ι → Submodule R A) :
    (upGradedRingHom 𝒜).comp (downGradedRingHom 𝒜) =
      GradedRingHom.id (submoduleFamily 𝒜) := sorry

end GradedRingHom

section HomogeneousAway

-- The Away carrier uses Mathlib's additive-subgroup homogeneous localization; a submodule over
-- a mere semiring is not closed under negation, so this comparison starts at `CommRing R`.
variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Algebra R A]
variable {ι : Type w} [AddCommMonoid ι] [DecidableEq ι]

/-- The homogeneous-away map induced by the upward graded ring homomorphism. -/
@[stacks 052N "universe-lifted homogeneous away map"]
noncomputable def awayUpMap (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {d : ι} (f : 𝒜 d) :
    Away 𝒜 (f : A) →+*
      Away (submoduleFamily 𝒜) (ULift.up (f : A) : ULift.{x} A) :=
  HomogeneousLocalization.Away.map (upGradedRingHom 𝒜) (f : A)

/-- The homogeneous-away map induced by the downward graded ring homomorphism. -/
@[stacks 052N "universe-lifted homogeneous away down map"]
noncomputable def awayDownMap (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {d : ι} (f : 𝒜 d) :
    Away (submoduleFamily 𝒜) (ULift.up (f : A) : ULift.{x} A) →+*
      Away 𝒜 (f : A) :=
  HomogeneousLocalization.Away.map (downGradedRingHom 𝒜)
    (ULift.up (f : A) : ULift.{x} A)

/-- The downward homogeneous-away map is a left inverse to the upward map. -/
@[stacks 052N "universe-lifted homogeneous away left inverse"]
theorem awayDown_leftInverse (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {d : ι} (f : 𝒜 d) :
    Function.LeftInverse (awayDownMap 𝒜 f) (awayUpMap 𝒜 f) := sorry

/-- The downward homogeneous-away map is a right inverse to the upward map. -/
@[stacks 052N "universe-lifted homogeneous away right inverse"]
theorem awayDown_rightInverse (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {d : ι} (f : 𝒜 d) :
    Function.RightInverse (awayDownMap 𝒜 f) (awayUpMap 𝒜 f) := sorry

/-- Homogeneous localization away from a homogeneous element commutes with
the canonical universe lift of an internally graded ring. -/
@[stacks 052N "universe-lifted homogeneous away ring equivalence"]
noncomputable def awayRingEquiv (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {d : ι} (f : 𝒜 d) :
    Away 𝒜 (f : A) ≃+*
      Away (submoduleFamily 𝒜) (ULift.up (f : A) : ULift.{x} A) where
  toFun := awayUpMap 𝒜 f
  invFun := awayDownMap 𝒜 f
  left_inv := awayDown_leftInverse 𝒜 f
  right_inv := awayDown_rightInverse 𝒜 f
  map_mul' := (awayUpMap 𝒜 f).map_mul
  map_add' := (awayUpMap 𝒜 f).map_add

/-- The homogeneous-away ring equivalence commutes with the base algebra map. -/
@[stacks 052N "universe-lifted homogeneous away algebra map"]
theorem awayRingEquiv_commutes (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {d : ι} (f : 𝒜 d) (r : R) :
    awayRingEquiv 𝒜 f (algebraMap R (Away 𝒜 (f : A)) r) =
      algebraMap R
        (Away (submoduleFamily 𝒜) (ULift.up (f : A) : ULift.{x} A)) r := sorry

/-- Homogeneous localization away from a homogeneous element is preserved as
an algebra by the canonical universe lift. -/
@[stacks 052N "universe-lifted homogeneous away algebra equivalence"]
noncomputable def awayAlgEquiv (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {d : ι} (f : 𝒜 d) :
    Away 𝒜 (f : A) ≃ₐ[R]
      Away (submoduleFamily 𝒜) (ULift.up (f : A) : ULift.{x} A) :=
  { toRingEquiv := awayRingEquiv 𝒜 f
    commutes' := awayRingEquiv_commutes 𝒜 f }

end HomogeneousAway

end ULift
