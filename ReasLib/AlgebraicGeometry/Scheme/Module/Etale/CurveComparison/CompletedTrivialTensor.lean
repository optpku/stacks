/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactResolution
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.CategoryTheory.Category.Preorder

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

namespace CompactRepresentation

variable (Λ G : Type u) [CommRing Λ] [Finite Λ]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Finite continuous quotient indices: actual open invariant submodules. -/
structure OpenInvariantSubmodule (M : Cat Λ G) where
  submodule : Submodule Λ M.obj.V.toModule
  isOpen : IsOpen (submodule : Set M.obj.V.toModule)
  stable : ∀ g : G, submodule ≤ submodule.comap (CompactModule.linear Λ (M.obj.ρ g))

namespace OpenInvariantSubmodule

variable {Λ G} {M : Cat Λ G}

instance : Preorder (OpenInvariantSubmodule Λ G M) where
  le U V := U.submodule ≤ V.submodule
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans

def quotient (U : OpenInvariantSubmodule Λ G M) := M.obj.V.toModule ⧸ U.submodule

instance (U : OpenInvariantSubmodule Λ G M) : AddCommGroup (quotient U) :=
  inferInstanceAs (AddCommGroup (M.obj.V.toModule ⧸ U.submodule))
instance (U : OpenInvariantSubmodule Λ G M) : Module Λ (quotient U) :=
  inferInstanceAs (Module Λ (M.obj.V.toModule ⧸ U.submodule))

instance finite_quotient (U : OpenInvariantSubmodule Λ G M) : Finite (quotient U) := by sorry

/-- The actual descended group action on the finite coefficient quotient. -/
def action (U : OpenInvariantSubmodule Λ G M) (g : G) : quotient U →ₗ[Λ] quotient U :=
  U.submodule.mapQ U.submodule (CompactModule.linear Λ (M.obj.ρ g)) (U.stable g)

def quotientMap {U V : OpenInvariantSubmodule Λ G M} (h : U ≤ V) :
    quotient U →ₗ[Λ] quotient V :=
  U.submodule.mapQ V.submodule LinearMap.id h

/-- Group-basis balancing for the RIGHT trivial module Λ and LEFT finite
quotient M/U. This is the explicit relative tensor presentation over Λ[G];
the continuous finite action factors through a finite group quotient. -/
def tensorRelations (U : OpenInvariantSubmodule Λ G M) :
    Submodule Λ (Λ ⊗[Λ] quotient U) :=
  Submodule.span Λ (Set.range (fun gax : G × Λ × quotient U ↦
    gax.2.1 ⊗ₜ[Λ] action U gax.1 gax.2.2 - gax.2.1 ⊗ₜ[Λ] gax.2.2))

def tensorCarrier (U : OpenInvariantSubmodule Λ G M) :=
  (Λ ⊗[Λ] quotient U) ⧸ tensorRelations U

instance (U : OpenInvariantSubmodule Λ G M) : AddCommGroup (tensorCarrier U) :=
  inferInstanceAs (AddCommGroup ((Λ ⊗[Λ] quotient U) ⧸ tensorRelations U))
instance (U : OpenInvariantSubmodule Λ G M) : Module Λ (tensorCarrier U) :=
  inferInstanceAs (Module Λ ((Λ ⊗[Λ] quotient U) ⧸ tensorRelations U))
instance finite_tensor (U : OpenInvariantSubmodule Λ G M) : Finite (tensorCarrier U) := by sorry

/-- Actual finite discrete tensor stage. -/
def tensorStage (U : OpenInvariantSubmodule Λ G M) : CompactModule Λ where
  toModule := ModuleCat.of Λ (tensorCarrier U)
  topology := ⊥
  compact := by sorry
  t2 := by sorry
  topologicalAdd := by sorry
  scalarContinuous := by sorry

def tensorMap {U V : OpenInvariantSubmodule Λ G M} (h : U ≤ V) : tensorStage U ⟶ tensorStage V :=
  { toLinearMap := (tensorRelations U).mapQ (tensorRelations V)
      (TensorProduct.map (LinearMap.id : Λ →ₗ[Λ] Λ) (quotientMap h)) (by sorry)
    cont := by sorry }

/-- Projection m ↦ [1 ⊗ (m mod U)], before taking compact coinvariants. -/
def projection (U : OpenInvariantSubmodule Λ G M) : M.obj.V.toModule →ₗ[Λ] tensorCarrier U :=
  (tensorRelations U).mkQ.comp
    ((TensorProduct.mk Λ Λ (quotient U) 1).comp U.submodule.mkQ)

theorem relations_le_kernel (U : OpenInvariantSubmodule Λ G M) :
    relations Λ G M ≤ LinearMap.ker (projection U) := by sorry

/-- The actual quotient map from continuous coinvariants to each tensor stage. -/
def fromCoinvariants (U : OpenInvariantSubmodule Λ G M) :
    coinvariants Λ G M ⟶ tensorStage U :=
  { toLinearMap := (relations Λ G M).liftQ (projection U) (relations_le_kernel U)
    cont := by sorry }

end OpenInvariantSubmodule

/-- All finite tensor stages and their actual quotient-induced maps. -/
def finiteTensorDiagram (M : Cat Λ G) : OpenInvariantSubmodule Λ G M ⥤ CompactModule Λ where
  obj := OpenInvariantSubmodule.tensorStage
  map f := OpenInvariantSubmodule.tensorMap (leOfHom f)
  map_id := by sorry
  map_comp := by sorry

instance finiteTensorDiagram_hasLimit (M : Cat Λ G) : HasLimit (finiteTensorDiagram Λ G M) := by sorry

/-- The independently constructed completed trivial tensor: inverse limit of
the finite balanced tensor stages, NOT defined as continuous coinvariants. -/
def completedTrivialTensor (M : Cat Λ G) : CompactModule Λ :=
  limit (finiteTensorDiagram Λ G M)

def tensorComparisonCone (M : Cat Λ G) : Cone (finiteTensorDiagram Λ G M) where
  pt := coinvariants Λ G M
  π :=
    { app := OpenInvariantSubmodule.fromCoinvariants
      naturality := by sorry }

/-- The comparison is the map with specified finite-stage projections. -/
def coinvariantsToCompletedTensor (M : Cat Λ G) :
    coinvariants Λ G M ⟶ completedTrivialTensor Λ G M :=
  limit.lift _ (tensorComparisonCone Λ G M)

/-- For compact G, open invariant submodules form a neighbourhood basis.
Thus the displayed finite-stage map realizes the closed coinvariant quotient. -/
instance coinvariantsToCompletedTensor_isIso [CompactSpace G] (M : Cat Λ G) :
    IsIso (coinvariantsToCompletedTensor Λ G M) := by sorry

def completedTensorComparison [CompactSpace G] (M : Cat Λ G) :
    coinvariants Λ G M ≅ completedTrivialTensor Λ G M :=
  asIso (coinvariantsToCompletedTensor Λ G M)

theorem completedTensorComparison_projection [CompactSpace G] (M : Cat Λ G)
    (U : OpenInvariantSubmodule Λ G M) :
    (completedTensorComparison Λ G M).hom ≫ limit.π (finiteTensorDiagram Λ G M) U =
      OpenInvariantSubmodule.fromCoinvariants U := by
  exact limit.lift_π _ _

end CompactRepresentation
