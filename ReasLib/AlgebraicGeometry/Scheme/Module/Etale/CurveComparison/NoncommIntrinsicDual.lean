/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommFiniteCoefficient

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace NoncommIntrinsicDual
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (NoncommFiniteCoefficient.modules R)]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))

/-- The actual local A-linear morphisms into roots, before rebundling their
correct right R-action. A is the lifted integer quotient of cardinality R. -/
def Carrier (U : Y.Etaleᵒᵖ) := (NoncommFiniteCoefficient.dual R Y F).obj.obj U

instance carrier_addCommGroup (U : Y.Etaleᵒᵖ) : AddCommGroup (Carrier R Y F U) :=
  inferInstanceAs (AddCommGroup ((NoncommFiniteCoefficient.dual R Y F).obj.obj U))

instance carrier_coefficientModule (U : Y.Etaleᵒᵖ) :
    Module (ActualRootsModule.Coeff.{u} (Nat.card R)) (Carrier R Y F U) :=
  inferInstanceAs (Module (ActualRootsModule.Coeff.{u} (Nat.card R))
    ((NoncommFiniteCoefficient.dual R Y F).obj.obj U))

/-- The actual right scalar endomorphisms on local Hom sections. -/
def sectionAction (U : Y.Etaleᵒᵖ) : Rᵐᵒᵖ →+*
    Module.End (ActualRootsModule.Coeff.{u} (Nat.card R)) (Carrier R Y F U) where
  toFun r := ((NoncommFiniteCoefficient.dualScalarEnd R Y F r).hom.app U).hom
  map_zero' := by sorry
  map_one' := by sorry
  map_add' := by sorry
  map_mul' := by sorry

/-- The Rᵐᵒᵖ-module structure is specified by local source precomposition. -/
instance carrier_rightModule (U : Y.Etaleᵒᵖ) : Module Rᵐᵒᵖ (Carrier R Y F U) :=
  Module.compHom (Carrier R Y F U) (sectionAction R Y F U)

/-- The local-Hom restriction maps, with their actual opposite-coefficient linearity. -/
def presheaf : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Rᵐᵒᵖ where
  obj U := ModuleCat.of Rᵐᵒᵖ (Carrier R Y F U)
  map f := ModuleCat.ofHom
    { toFun := fun φ ↦ ((NoncommFiniteCoefficient.dual R Y F).obj.map f).hom φ
      map_add' := by intros; exact map_add _ _ _
      map_smul' := by sorry }
  map_id := by sorry
  map_comp := by sorry

/-- Gluing is the existing local-Hom sheaf gluing on exactly the same sections. -/
theorem isSheaf : Presheaf.IsSheaf Y.smallEtaleTopology (presheaf R Y F) := by sorry

/-- The genuine intrinsic RIGHT R dual sheaf, including the roots-of-unity twist. -/
def obj : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ) :=
  ⟨presheaf R Y F, isSheaf R Y F⟩

/-- Concrete local evaluation of a source vector against an intrinsic dual section. -/
def evaluation (U : Y.Etaleᵒᵖ)
    (m : ((NoncommFiniteCoefficient.sheaves R Y).obj F).obj.obj U)
    (φ : (obj R Y F).obj.obj U) :
    (ActualRootsModule.liftedSheaf Y (Nat.card R)).obj.obj U :=
  NoncommFiniteCoefficient.evaluation R Y F U m φ

/-- The left/right balance is inherited from actual source precomposition. -/
theorem evaluation_balanced (U : Y.Etaleᵒᵖ) (r : R)
    (m : ((NoncommFiniteCoefficient.sheaves R Y).obj F).obj.obj U)
    (φ : (obj R Y F).obj.obj U) :
    evaluation R Y F U (((NoncommFiniteCoefficient.scalarEnd R Y F r).hom.app U).hom m) φ =
      evaluation R Y F U m (MulOpposite.op r • φ) := rfl

end NoncommIntrinsicDual
