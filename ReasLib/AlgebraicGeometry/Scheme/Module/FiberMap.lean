module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberRank

/-!
# Maps on fibers of scheme modules

A morphism of scheme modules induces a linear map between the residue-field fibers at every
point.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The residue-field linear map on fibers induced by a morphism of scheme modules. -/
noncomputable def fiberMap {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) (x : X) :
    fiber ℱ x →ₗ[IsLocalRing.ResidueField (X.presheaf.stalk x)] fiber 𝒢 x :=
  (RingedSpace.moduleStalkHom x φ).hom.baseChange
    (IsLocalRing.ResidueField (X.presheaf.stalk x))

/-- On a pure tensor, the induced fiber map applies the stalk map to the module factor. -/
@[simp]
theorem fiberMap_tmul {ℱ 𝒢 : X.Modules} (φ : ℱ ⟶ 𝒢) (x : X)
    (a : IsLocalRing.ResidueField (X.presheaf.stalk x))
    (m : RingedSpace.stalkModuleCat ℱ x) :
    fiberMap φ x (a ⊗ₜ m) = a ⊗ₜ (RingedSpace.moduleStalkHom x φ).hom m := sorry

end AlgebraicGeometry.Scheme.Modules
