/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactCompletedAction

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u

namespace ActualCompactCompletedModules
variable (Λ G : Type u) [CommRing Λ] [Finite Λ]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- The module action is Kuhn's actual inverse-limit completed action. -/
def obj (M : CompactRepresentation.Cat Λ G) : ModuleCat.{u} (completedGroupRing Λ G) :=
  -- Local instance justification (defeq pin): define the action by the specified completed-action ring homomorphism.
  letI := Module.compHom M.obj.V.toModule (CompactRepresentation.completedAction Λ G M)
  ModuleCat.of (completedGroupRing Λ G) M.obj.V.toModule

/-- Continuous equivariant linear maps commute with every finite-stage
completed action, hence with its inverse-limit action. -/
theorem map_completedAction {M N : CompactRepresentation.Cat Λ G} (f : M ⟶ N)
    (r : completedGroupRing Λ G) (x : M.obj.V.toModule) :
    CompactModule.linear Λ f.hom.hom (CompactRepresentation.completedAction Λ G M r x) =
    CompactRepresentation.completedAction Λ G N r (CompactModule.linear Λ f.hom.hom x) := sorry

def map {M N : CompactRepresentation.Cat Λ G} (f : M ⟶ N) : obj Λ G M ⟶ obj Λ G N :=
  -- Local instance justification (defeq pin): use exactly the source and target completed actions defining obj.
  letI := Module.compHom M.obj.V.toModule (CompactRepresentation.completedAction Λ G M)
  -- Local instance justification (defeq pin): use the identical target action chosen by obj.
  letI := Module.compHom N.obj.V.toModule (CompactRepresentation.completedAction Λ G N)
  ModuleCat.ofHom (show obj Λ G M →ₗ[completedGroupRing Λ G] obj Λ G N from
    { toFun := CompactModule.linear Λ f.hom.hom
      map_add' := (CompactModule.linear Λ f.hom.hom).map_add
      map_smul' := map_completedAction Λ G f })

def functor : CompactRepresentation.Cat Λ G ⥤ ModuleCat.{u} (completedGroupRing Λ G) where
  obj := obj Λ G
  map := map Λ G
  map_id := sorry
  map_comp := sorry

instance functor_additive : (functor Λ G).Additive := sorry

/-- Forgetting compact topology is exact here: continuous images of compact
modules in Hausdorff modules are already closed. -/
instance functor_preservesFiniteLimits : PreservesFiniteLimits (functor Λ G) := sorry
instance functor_preservesFiniteColimits : PreservesFiniteColimits (functor Λ G) := sorry

end ActualCompactCompletedModules
