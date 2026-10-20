/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompletedTensorDerived

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace CompactRepresentation

variable (Λ G : Type u) [CommRing Λ] [hΛ : Finite Λ]
variable [Group G] [TopologicalSpace G] [hG : IsTopologicalGroup G] [hcG : CompactSpace G]

/-- Finite continuous quotient with its actual discrete topology. -/
def finiteQuotientStage (M : Cat Λ G) (U : OpenInvariantSubmodule Λ G M) :
    CompactModule Λ where
  toModule := ModuleCat.of Λ (OpenInvariantSubmodule.quotient U)
  topology := ⊥
  compact := by sorry
  t2 := by sorry
  topologicalAdd := by sorry
  scalarContinuous := by sorry

def finiteQuotientMap {M : Cat Λ G} {U V : OpenInvariantSubmodule Λ G M} (h : U ≤ V) :
    finiteQuotientStage Λ G M U ⟶ finiteQuotientStage Λ G M V :=
  { toLinearMap := OpenInvariantSubmodule.quotientMap h
    cont := by sorry }

def finiteQuotientDiagram (M : Cat Λ G) :
    OpenInvariantSubmodule Λ G M ⥤ CompactModule Λ where
  obj := finiteQuotientStage Λ G M
  map f := finiteQuotientMap Λ G (leOfHom f)
  map_id := by sorry
  map_comp := by sorry

instance (M : Cat Λ G) : HasLimit (finiteQuotientDiagram Λ G M) := by sorry

def finiteQuotientProjection (M : Cat Λ G) (U : OpenInvariantSubmodule Λ G M) :
    M.obj.V ⟶ finiteQuotientStage Λ G M U :=
  { toLinearMap := U.submodule.mkQ
    cont := by sorry }

def finiteQuotientCone (M : Cat Λ G) : Cone (finiteQuotientDiagram Λ G M) where
  pt := M.obj.V
  π :=
    { app := finiteQuotientProjection Λ G M
      naturality := by sorry }

/-- The comparison is specified by ALL actual finite quotient projections. -/
def toFiniteQuotientLimit (M : Cat Λ G) : M.obj.V ⟶ limit (finiteQuotientDiagram Λ G M) :=
  limit.lift _ (finiteQuotientCone Λ G M)

/-- Finite coefficients give a profinite additive group; compactness of G
makes invariant open submodules cofinal in its neighbourhood basis. -/
instance toFiniteQuotientLimit_isIso [Finite Λ] [IsTopologicalGroup G] [CompactSpace G]
    (M : Cat Λ G) :
    IsIso (toFiniteQuotientLimit Λ G M) := by sorry

def finiteQuotientLimitIso (M : Cat Λ G) : M.obj.V ≅ limit (finiteQuotientDiagram Λ G M) :=
  asIso (toFiniteQuotientLimit Λ G M)

theorem finiteQuotientLimitIso_projection (M : Cat Λ G) (U : OpenInvariantSubmodule Λ G M) :
    (finiteQuotientLimitIso Λ G M).hom ≫ limit.π (finiteQuotientDiagram Λ G M) U =
      finiteQuotientProjection Λ G M U := by
  exact limit.lift_π _ _

/-- The completed ring acts through the actual finite action kernel. -/
def finiteCompletedEnd (M : Cat Λ G) (U : OpenInvariantSubmodule Λ G M)
    (r : completedGroupRing Λ G) : finiteQuotientStage Λ G M U ⟶ finiteQuotientStage Λ G M U :=
  { toLinearMap := finiteCompletedAction Λ G M U r
    cont := by sorry }

/-- Compatibility is imposed on these explicit finite actions, not supplied
as an arbitrary realization or ring-action witness. -/
theorem finiteCompletedEnd_naturality (M : Cat Λ G)
    {U V : OpenInvariantSubmodule Λ G M} (h : U ≤ V) (r : completedGroupRing Λ G) :
    finiteCompletedEnd Λ G M U r ≫ finiteQuotientMap Λ G h =
      finiteQuotientMap Λ G h ≫ finiteCompletedEnd Λ G M V r := by sorry

def completedEndCone (M : Cat Λ G) (r : completedGroupRing Λ G) :
    Cone (finiteQuotientDiagram Λ G M) where
  pt := limit (finiteQuotientDiagram Λ G M)
  π :=
    { app := fun U ↦ limit.π (finiteQuotientDiagram Λ G M) U ≫ finiteCompletedEnd Λ G M U r
      naturality := by sorry }

/-- Endomorphism constructed by the universal property of the inverse limit. -/
def completedEndOnLimit (M : Cat Λ G) (r : completedGroupRing Λ G) :
    limit (finiteQuotientDiagram Λ G M) ⟶ limit (finiteQuotientDiagram Λ G M) :=
  limit.lift _ (completedEndCone Λ G M r)

/-- Actual action on the given compact module, transported by the specified
finite-quotient comparison, not by an independent isomorphism. -/
def completedEnd (M : Cat Λ G) (r : completedGroupRing Λ G) : M.obj.V ⟶ M.obj.V :=
  (finiteQuotientLimitIso Λ G M).hom ≫ completedEndOnLimit Λ G M r ≫
    (finiteQuotientLimitIso Λ G M).inv

def completedAction (M : Cat Λ G) : completedGroupRing Λ G →+* Module.End Λ M.obj.V.toModule where
  toFun r := CompactModule.linear Λ (completedEnd Λ G M r)
  map_zero' := by sorry
  map_one' := by sorry
  map_add' := by sorry
  map_mul' := by sorry

theorem completedAction_projection (M : Cat Λ G) (U : OpenInvariantSubmodule Λ G M)
    (r : completedGroupRing Λ G) (m : M.obj.V.toModule) :
    U.submodule.mkQ (completedAction Λ G M r m) =
      finiteCompletedAction Λ G M U r (U.submodule.mkQ m) := by sorry

/-- The action recovers the original coefficient action. -/
theorem completedAction_scalar (M : Cat Λ G) (a : Λ) (m : M.obj.V.toModule) :
    completedAction Λ G M (completedGroupRing.ofScalar Λ G a) m = a • m := by sorry

/-- Every ring element acts by the continuous map actually constructed above. -/
theorem completedAction_continuous (M : Cat Λ G) (r : completedGroupRing Λ G) :
    Continuous (completedAction Λ G M r) :=
  (show M.obj.V.toModule →L[Λ] M.obj.V.toModule from completedEnd Λ G M r).cont

end CompactRepresentation
