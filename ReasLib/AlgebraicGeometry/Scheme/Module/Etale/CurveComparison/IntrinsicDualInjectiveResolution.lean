/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LocalHomResolutionAugmentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LocalHomIntrinsicBridge
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteAssociatedResolution
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.OpenExtensionInjectiveResolution

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace IntrinsicDualInjectiveResolution
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable (X : SchemeOverField k) [ConnectedSpace X.left]
variable (x : GeometricPoint X.left)
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R)))]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose (NoncommFiniteCoefficient.modules R)]
variable [∀ Y : Scheme.{u}, EnoughInjectives (Sheaf Y.smallEtaleTopology
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R))))]
variable [∀ {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
  (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R))),
  (etaleRestriction j).op.HasLeftKanExtension F]
variable (M : (finiteTypeDiscreteModule R (Aut (standardFiniteEtaleFiber x))).FullSubcategory)

abbrev source := (associatedSheafFunctor R x).obj M
abbrev sourceResolution := FiniteAssociatedResolution.complex R x M
abbrev rootsResolution := OpenExtensionInjectiveResolution.resolution
  (ActualRootsModule.Coeff.{u} (Nat.card R)) (Compactification.Of.ι P)
    (ActualRootsModule.liftedSheaf X.left (Nat.card R))

/-- Reuse Kuhn's actual finite-diagonal Hom differential, with source resolution
from the published finite inverse and target restricted from the SAME compactification. -/
def complex := NoncommLocalHomComplex.complex (NoncommFiniteCoefficient.scalarHom R)
  (NoncommFiniteCoefficient.scalarHom_commute R) X.left (sourceResolution R X x M)
    (rootsResolution R X P).cocomplex

/-- The actual intrinsic dual enters via identity on local transformations,
source precomposition, and the actual roots-resolution augmentation. -/
def augmentation : (CochainComplex.single₀ _).obj
    (NoncommIntrinsicDual.obj R X.left (source R X x M)) ⟶ complex R X x P M :=
  (CochainComplex.single₀ _).map (LocalHomIntrinsicBridge.iso R X.left (source R X x M)).hom ≫
  LocalHomResolutionAugmentation.map (NoncommFiniteCoefficient.scalarHom R)
    (NoncommFiniteCoefficient.scalarHom_commute R) X.left (sourceResolution R X x M)
    (rootsResolution R X P).cocomplex (FiniteAssociatedResolution.augmentation R x M)
    (rootsResolution R X P).ι

/-- Every stalk is the finite coefficient-projective term, not a projective
object of the finite or all-discrete representation category. -/
theorem source_stalk_projective (y : GeometricPoint X.left) (i : ℕ) :
    Module.Projective R ((StalkRepresentation.stalk R y).obj ((sourceResolution R X x M).X i)) := by sorry

/-- Explicit remaining PROOF obligation: local R-flatness of the source terms
and A-injectivity of the target terms make the finite Hom diagonals injective.
The plain-sheaf balanced tensor adjunction proof is not supplied by Kuhn's payload. -/
theorem term_injective (i : ℕ) : Injective ((complex R X x P M).X i) := by sorry

variable (hR : IsUnit (Nat.card R : k))
include hR in
/-- Finite locally constant source and invertible n make roots locally rank-one
over the self-injective Z/n. Thus this SPECIFIED augmentation computes the
intrinsic dual on X; it makes no concentration claim for Rj_* on P. -/
theorem augmentation_quasiIso : QuasiIso (augmentation R X x P M) := by sorry

/-- Explicit resolution data. Its injectivity and quasi-isomorphism remain the
named true Prop obligations above, not arbitrary assumed comparison packages. -/
def resolution : InjectiveResolution (NoncommIntrinsicDual.obj R X.left (source R X x M)) where
  cocomplex := complex R X x P M
  injective := term_injective R X x P M
  ι := augmentation R X x P M
  quasiIso := augmentation_quasiIso R X x P M hR

variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ))]

/-- The actual recursive comparison from the existing intrinsic-dual resolution
to the constructed Hom resolution, with genuine hom/inv and homotopies. -/
def comparison := InjectiveResolution.homotopyEquiv
  (injectiveResolution (NoncommIntrinsicDual.obj R X.left (source R X x M))) (resolution R X x P M hR)

end IntrinsicDualInjectiveResolution
