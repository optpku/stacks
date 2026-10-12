/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommLocalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommIntrinsicDual

@[expose] public section
open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace LocalHomIntrinsicBridge
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (NoncommFiniteCoefficient.modules R)]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))

/-- Kuhn's arbitrary-target Hom specializes to the EXISTING intrinsic roots
dual by identity on actual local natural transformations, including the right R-action. -/
def iso : NoncommIntrinsicDual.obj R Y F ≅
    NoncommLocalHom.obj (NoncommFiniteCoefficient.scalarHom R)
      (NoncommFiniteCoefficient.scalarHom_commute R) Y F
      (ActualRootsModule.liftedSheaf Y (Nat.card R)) where
  hom := ObjectProperty.homMk
    { app := fun _ ↦ ModuleCat.ofHom
        { toFun := fun α ↦ α
          map_add' := by intros; rfl
          map_smul' := by sorry }
      naturality := by sorry }
  inv := ObjectProperty.homMk
    { app := fun _ ↦ ModuleCat.ofHom
        { toFun := fun α ↦ α
          map_add' := by intros; rfl
          map_smul' := by sorry }
      naturality := by sorry }
  hom_inv_id := by sorry
  inv_hom_id := by sorry

end LocalHomIntrinsicBridge
