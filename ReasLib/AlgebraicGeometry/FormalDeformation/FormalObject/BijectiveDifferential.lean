/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Derivation
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Differential
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.FiberIsoClass
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor

/-!
# Versal formal objects with bijective differential

A versal formal object with bijective differential implies Schlessinger's second
condition. Its differential identifies the tangent space with the finite-dimensional
space of residue-valued derivations, compatibly with the natural tangent operations.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

namespace CategoryTheory.Functor

/-- A predeformation category with a versal formal object whose differential is
bijective satisfies Schlessinger's condition (S2). -/
theorem hasSchlessingerS2_of_bijectiveDifferential
    [IsPredeformationCategory p] (ξ : FormalObject p) [FormalObject.IsVersal ξ]
    (h : FormalObject.BijectiveDifferential ξ) :
    HasSchlessingerS2 p := sorry

/-- Inverse of `FormalObject.differential ξ`, as an equivalence `tangentSpace p ≃
Derivation Λ ξ.base.carrier k` obtained from `FormalObject.BijectiveDifferential`. -/
noncomputable def tangentSpaceEquivDerivation
    [IsPredeformationCategory p] (ξ : FormalObject p)
    (h : FormalObject.BijectiveDifferential ξ) :
    tangentSpace p ≃ Derivation Λ ξ.base.carrier k :=
  (Equiv.ofBijective (FormalObject.differential ξ) h).symm

/-- `tangentSpaceEquivDerivation` inverts `FormalObject.differential`. -/
theorem tangentSpaceEquivDerivation_symm_apply
    [IsPredeformationCategory p] (ξ : FormalObject p)
    (h : FormalObject.BijectiveDifferential ξ)
    (D : Derivation Λ ξ.base.carrier k) :
    (tangentSpaceEquivDerivation ξ h).symm D = FormalObject.differential ξ D := sorry

/-- Additive group structure on `tangentSpace p` transported from
`Derivation Λ ξ.base.carrier k` along `tangentSpaceEquivDerivation`. -/
noncomputable abbrev tangentSpaceAddCommGroup
    [IsPredeformationCategory p] (ξ : FormalObject p)
    (h : FormalObject.BijectiveDifferential ξ) :
    AddCommGroup (tangentSpace p) :=
  Equiv.addCommGroup (tangentSpaceEquivDerivation ξ h)

/-- Addition on `tangentSpaceAddCommGroup` is transport of addition of derivations. -/
theorem tangentSpaceAddCommGroup_add
    [IsPredeformationCategory p] (ξ : FormalObject p)
    (h : FormalObject.BijectiveDifferential ξ)
    (x y : tangentSpace p) :
    (tangentSpaceAddCommGroup ξ h).add x y =
      (tangentSpaceEquivDerivation ξ h).symm
        (tangentSpaceEquivDerivation ξ h x + tangentSpaceEquivDerivation ξ h y) := sorry

/-- `k`-module structure on `tangentSpace p` transported from
`Derivation Λ ξ.base.carrier k` along `tangentSpaceEquivDerivation`, using the same
additive group as `tangentSpaceAddCommGroup`. -/
noncomputable abbrev tangentSpaceModule
    [IsPredeformationCategory p] (ξ : FormalObject p)
    (h : FormalObject.BijectiveDifferential ξ) :=
  Equiv.module k (tangentSpaceEquivDerivation ξ h)

/-- Scalar multiplication on `tangentSpaceModule` is transport of the `k`-action on
derivations. -/
theorem tangentSpaceModule_smul
    [IsPredeformationCategory p] (ξ : FormalObject p)
    (h : FormalObject.BijectiveDifferential ξ) (c : k) (x : tangentSpace p) :
    (tangentSpaceModule ξ h).smul c x =
      (tangentSpaceEquivDerivation ξ h).symm (c • tangentSpaceEquivDerivation ξ h x) := sorry

/-- The tangent space of a predeformation category admitting a versal formal object
with bijective differential is finite-dimensional for the module structure transported
from residue-valued derivations. -/
theorem finiteDimensional_tangentSpace_of_bijectiveDifferential
    [IsPredeformationCategory p] (ξ : FormalObject p) [FormalObject.IsVersal ξ]
    (h : FormalObject.BijectiveDifferential ξ) :
    @FiniteDimensional k (tangentSpace p) inferInstance
      (tangentSpaceAddCommGroup ξ h) (tangentSpaceModule ξ h) := sorry

/-- Addition transported through a bijective differential agrees with the natural
addition defined by the dual-number pullback comparison. -/
theorem tangentSpaceAddCommGroup_add_eq_canonical
    [IsPredeformationCategory p] [HasSchlessingerH2 (fiberIsoClassFunctor p)]
    (ξ : FormalObject p) (h : FormalObject.BijectiveDifferential ξ)
    (x y : tangentSpace p) :
    (tangentSpaceAddCommGroup ξ h).add x y = addFiberDualTangent p x y := sorry

/-- Scalar multiplication transported through a bijective differential agrees with
the natural action induced by scaling the dual numbers. -/
theorem tangentSpaceModule_smul_eq_canonical
    [IsPredeformationCategory p] [HasSchlessingerH2 (fiberIsoClassFunctor p)]
    (ξ : FormalObject p) (h : FormalObject.BijectiveDifferential ξ)
    (c : k) (x : tangentSpace p) :
    (tangentSpaceModule ξ h).smul c x = smulFiberDualTangent p c x := sorry

end CategoryTheory.Functor
