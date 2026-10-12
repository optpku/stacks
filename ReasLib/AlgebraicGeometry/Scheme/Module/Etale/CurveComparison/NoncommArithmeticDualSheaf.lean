/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommArithmeticDualStalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommIntrinsicDualTransport

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace NoncommArithmeticDualSheaf
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (η : GeometricPoint (geometricBaseChange X))
variable [X.left.smallEtaleTopology.HasSheafCompose (NoncommFiniteCoefficient.modules R)]
variable [X.left.smallEtaleTopology.HasSheafCompose (NoncommIntrinsicDualTransport.modules R)]
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [HasWeakSheafify X.left.smallEtaleTopology
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R)))]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U)
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R)))]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable (hR : IsUnit (Nat.card R : k))
variable (M : (finiteTypeDiscreteModule R
  (Aut (standardFiniteEtaleFiber (arithmeticPoint X η)))).FullSubcategory)

/-- The intrinsic right-coefficient roots dual on arithmetic X. -/
abbrev intrinsic := NoncommIntrinsicDual.obj R X.left
  (NoncommArithmeticDualStalk.sourceSheaf R X η M)

include hR in
/-- Finite local coefficients and invertible order make this roots dual finite locally constant. -/
theorem intrinsic_finite : Sheaf.IsFiniteTypeLocallyConstantModule (intrinsic R X η M) := by sorry

/-- The actual intrinsic dual as an input to the published forward equivalence. -/
def finiteIntrinsic : (Sheaf.finiteTypeLocallyConstantModule X.left.smallEtaleTopology Rᵐᵒᵖ).FullSubcategory :=
  ⟨intrinsic R X η M, intrinsic_finite R X η hR M⟩

/-- The specified germ/root/counit function, rebundled with its correct RIGHT
coefficient linearity. No arbitrary stalk isomorphism is selected. -/
def stalkMap :
    (StalkRepresentation.stalk Rᵐᵒᵖ (arithmeticPoint X η)).obj (intrinsic R X η M) →ₗ[Rᵐᵒᵖ]
    (NoncommArithmeticDualCoefficient.representation R X η hR M).obj.obj.V where
  toFun α :=
    NoncommArithmeticDualStalk.toCharacter R X η hR M
      ((NoncommIntrinsicDualTransport.stalkIso R X.left
        (NoncommArithmeticDualStalk.sourceSheaf R X η M) (arithmeticPoint X η)).hom α)
  map_add' := by sorry
  map_smul' := by sorry

/-- Bijectivity of the actual composite of filtered-stalk identity and character evaluation. -/
theorem stalkMap_bijective : Function.Bijective (stalkMap R X η hR M) := by sorry

/-- The specified linear equivalence of right-coefficient stalk modules. -/
def stalkEquiv := LinearEquiv.ofBijective (stalkMap R X η hR M)
  (stalkMap_bijective R X η hR M)

/-- Arithmetic monodromy acts on roots by the actual cyclotomic character;
contragredient inverse Tate action gives precisely the same map. -/
theorem stalkEquiv_equivariant
    (g : Aut (standardFiniteEtaleFiber (arithmeticPoint X η))) :
    ((finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Rᵐᵒᵖ (arithmeticPoint X η)).obj
      (finiteIntrinsic R X η hR M)).obj.obj.ρ g ≫ (stalkEquiv R X η hR M).toModuleIso.hom =
    (stalkEquiv R X η hR M).toModuleIso.hom ≫
      (NoncommArithmeticDualCoefficient.representation R X η hR M).obj.obj.ρ g := by sorry

/-- The actual arithmetic representation comparison, retaining its right scalars and action. -/
def representationIso :
    (finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Rᵐᵒᵖ (arithmeticPoint X η)).obj
      (finiteIntrinsic R X η hR M) ≅
    NoncommArithmeticDualCoefficient.representation R X η hR M :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (Action.mkIso (stalkEquiv R X η hR M).toModuleIso (stalkEquiv_equivariant R X η hR M)))

/-- Full arithmetic sheaf comparison: the published unit, followed by the
published inverse applied to the explicit linear equivariant stalk map. -/
def iso : intrinsic R X η M ≅ (NoncommArithmeticDualCoefficient.sheaf R X η hR M).obj :=
  (Sheaf.finiteTypeLocallyConstantModule X.left.smallEtaleTopology Rᵐᵒᵖ).ι.mapIso
    (((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules
      Rᵐᵒᵖ (arithmeticPoint X η)).unitIso.app (finiteIntrinsic R X η hR M)) ≪≫
      (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules
        Rᵐᵒᵖ (arithmeticPoint X η)).inverse.mapIso (representationIso R X η hR M))

end NoncommArithmeticDualSheaf
