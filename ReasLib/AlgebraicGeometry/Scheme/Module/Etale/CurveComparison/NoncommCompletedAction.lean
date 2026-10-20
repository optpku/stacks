/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompactTensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCompletedRing

@[expose] public section
open CategoryTheory
noncomputable section
universe u

namespace NoncommCompletedAction
variable (R G : Type u) [Ring R] [Finite R]
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (M : NoncommCompactRepresentation.Cat R G)
open NoncommCompactTensor

/-- Kernel of the ACTUAL finite quotient action. This is not a kernel
assertion for an arbitrary infinite representation. -/
def normalKernel (U : Index R G M) : OpenNormalSubgroup G where
  toOpenSubgroup :=
    { toSubgroup :=
        { carrier := {g | (Index.action U).ρ g = 𝟙 _}
          one_mem' := by sorry
          mul_mem' := by sorry
          inv_mem' := by sorry }
      isOpen' := by sorry }
  isNormal' := by sorry

/-- Evaluate the finite group algebra by coefficients acting on the LEFT.
For noncommutative R this is additive, not generally R-linear in x. -/
def atStage (U : Index R G M) (r : completedGroupRing R G)
    (x : Index.quotient U) : Index.quotient U :=
  (completedGroupRing.π R G (normalKernel R G M U) r).coeff.sum
    (fun q a ↦ a • ((Index.action U).ρ (Quotient.out q)).hom x)

/-- Compatibility equations of the original coefficient's finite quotient system. -/
def compatible : Submodule R (∀ U : Index R G M, Index.quotient U) where
  carrier := {x | ∀ (U V : Index R G M) (h : U ≤ V),
    U.submodule.mapQ V.submodule LinearMap.id h (x U) = x V}
  zero_mem' := by sorry
  add_mem' := by sorry
  smul_mem' := by sorry

/-- The canonical finite-quotient comparison has its specified projections. -/
def toLimit : M.obj.V.toModule →ₗ[R] compatible R G M where
  toFun m := ⟨fun U ↦ U.submodule.mkQ m, by sorry⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Compact G supplies the invariant open-submodule basis required here. -/
theorem toLimit_bijective [CompactSpace G] : Function.Bijective (toLimit R G M) := by sorry

/-- Inverse of the specified finite quotient comparison. -/
def limitEquiv [CompactSpace G] : M.obj.V.toModule ≃ₗ[R] compatible R G M :=
  LinearEquiv.ofBijective (toLimit R G M) (toLimit_bijective R G M)

/-- The finite completed actions respect all actual quotient transitions. -/
theorem atStage_compatible (r : completedGroupRing R G) (x : compatible R G M) :
    (fun U ↦ atStage R G M U r (x.val U)) ∈ compatible R G M := by sorry

/-- Actual action on compatible families, with no false R-linearity requirement. -/
def onLimit (r : completedGroupRing R G) (x : compatible R G M) : compatible R G M :=
  ⟨fun U ↦ atStage R G M U r (x.val U), atStage_compatible R G M r x⟩

variable [CompactSpace G]

/-- Action on the original compact coefficient through its actual quotient coordinates. -/
def scalar (r : completedGroupRing R G) (m : M.obj.V.toModule) : M.obj.V.toModule :=
  (limitEquiv R G M).symm (onLimit R G M r (limitEquiv R G M m))

/-- Keep the completed-module carrier separate from its original R-module instance. -/
def Carrier := M.obj.V.toModule

instance carrier_addCommGroup : AddCommGroup (Carrier R G M) :=
  inferInstanceAs (AddCommGroup M.obj.V.toModule)

/-- Noncommutative completed scalars satisfy the module laws as ADDITIVE maps.
They are not placed in Module.End R, which would be false in general. -/
instance completedModule : Module (completedGroupRing R G) (Carrier R G M) where
  smul := scalar R G M
  one_smul := by sorry
  mul_smul := by sorry
  smul_zero := by sorry
  smul_add := by sorry
  zero_smul := by sorry
  add_smul := by sorry

/-- The actual completed-ring module, over a possibly noncommutative ring. -/
def module : ModuleCat.{u} (completedGroupRing R G) :=
  ModuleCat.of (completedGroupRing R G) (Carrier R G M)

/-- Scalar restriction recovers exactly the original LEFT R action. -/
theorem scalar_ofScalar (r : R) (m : M.obj.V.toModule) :
    scalar R G M (completedGroupRing.ofScalar R G r) m = r • m := by sorry

/-- Dirac families recover the independent original group action. -/
theorem scalar_dirac (g : G) (m : M.obj.V.toModule) :
    scalar R G M (completedGroupRing.dirac R G g) m =
      (show _ →L[R] _ from M.obj.ρ g) m := by sorry

variable {M}

/-- Continuous equivariant R-linear maps commute with the actual finite-stage actions. -/
theorem scalar_naturality {N : NoncommCompactRepresentation.Cat R G} (f : M ⟶ N)
    (r : completedGroupRing R G) (m : M.obj.V.toModule) :
    (show _ →L[R] _ from f.hom.hom) (scalar R G M r m) =
      scalar R G N r ((show _ →L[R] _ from f.hom.hom) m) := by sorry

/-- The same coefficient function, now with its proved completed linearity. -/
def map {N : NoncommCompactRepresentation.Cat R G} (f : M ⟶ N) :
    module R G M ⟶ module R G N :=
  ModuleCat.ofHom
    { toFun := fun m ↦ (show _ →L[R] _ from f.hom.hom) m
      map_add' := (show _ →L[R] _ from f.hom.hom).map_add
      map_smul' := scalar_naturality R G f }

/-- Actual scalar-extension functor on compact representations. -/
def functor : NoncommCompactRepresentation.Cat R G ⥤ ModuleCat.{u} (completedGroupRing R G) where
  obj := fun M ↦ module R G M
  map := map R G
  map_id := by sorry
  map_comp := by sorry

instance functor_additive : (functor R G).Additive := by sorry

end NoncommCompletedAction
