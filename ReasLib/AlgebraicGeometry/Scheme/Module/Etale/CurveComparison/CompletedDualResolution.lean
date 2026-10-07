module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ResidualCompletedTarget
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace ActualCompletedDualResolution
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (ηbar : GeometricPoint (geometricBaseChange X))
variable (K : CompactRepresentation.Cat Λ
    (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar))))

/-- Resolve the actual continuous character module in ALL discrete arithmetic
representations. Neither finite-category injectives nor algebraic biduality
are used. -/
abbrev characterResolution := injectiveResolution
  (CompactRepresentation.continuousDual Λ
    (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar))) K)

/-- Kuhn's specified dual differentials and continuous evaluation augmentation. -/
abbrev compactResolution := CompactRepresentation.compactProjectiveResolution Λ
  (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar))) K
  (characterResolution Λ X ηbar K)

/-- The actual projective resolution lift, before taking residual coinvariants. -/
def arithmeticComparison := ProjectiveResolution.homotopyEquiv
  (compactResolution Λ X ηbar K) (ActualResidualCompletedTarget.resolution Λ X ηbar K)

/-- The residual action and completed scalars are retained through every
component of the resolution comparison, not recovered from homology. -/
def completedComparison :=
  (CompactResidual.geometricCoinvariantsFunctor Λ X ηbar ⋙
    ActualResidualCompletedTarget.toGaloisModules Λ X ηbar).mapHomotopyEquiv
      (arithmeticComparison Λ X ηbar K)

/-- The concrete completed dual-resolution complex in curve degrees 2-i. -/
def galoisCochain :=
  (((CompactResidual.geometricCoinvariantsFunctor Λ X ηbar ⋙
    ActualResidualCompletedTarget.toGaloisModules Λ X ηbar).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (compactResolution Λ X ηbar K).complex).extend
        CompactRepresentation.curveDegreeEmbedding

/-- Actual extended chain lift to the already assembled compact target. -/
def toNative : galoisCochain Λ X ηbar K ⟶
    ActualResidualCompletedTarget.galoisCochain Λ X ηbar K :=
  HomologicalComplex.extendMap (completedComparison Λ X ηbar K).hom
    CompactRepresentation.curveDegreeEmbedding

instance toNative_quasiIso : QuasiIso (toNative Λ X ηbar K) := by
  unfold toNative
  exact (HomologicalComplex.quasiIso_extendMap_iff _ _).2
    (HomotopyEquiv.quasiIso_hom (completedComparison Λ X ηbar K))

section GaloisDerived
variable [HasDerivedCategory (ModuleCat.{u + 1}
    (completedGroupRing Λ Gal(AlgebraicClosure k/k)))]

/-- The resolution comparison in the actual residual Galois category for an
arbitrary base field. No finite-field identification is used. -/
def nativeGaloisDerivedIso : DerivedCategory.Q.obj (galoisCochain Λ X ηbar K) ≅
    DerivedCategory.Q.obj (ActualResidualCompletedTarget.galoisCochain Λ X ηbar K) :=
  asIso (DerivedCategory.Q.map (toNative Λ X ηbar K))

/-- Complete target-side composition over the original residual Galois group,
retaining general k and the explicit inverse-Tate coefficient. -/
def finiteInputTensorGaloisIso (hΛ : IsUnit (Nat.card Λ : k))
    (M : (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory) :
    DerivedCategory.Q.obj (galoisCochain Λ X ηbar
      (ActualArithmeticDualSheaf.compactInput Λ X ηbar hΛ M)) ≅
    DerivedCategory.Q.obj (ActualResidualCompletedTarget.tensorGaloisCochain Λ X ηbar
      (ActualArithmeticDualSheaf.compactInput Λ X ηbar hΛ M)) :=
  nativeGaloisDerivedIso Λ X ηbar (ActualArithmeticDualSheaf.compactInput Λ X ηbar hΛ M) ≪≫
    DerivedCategory.Q.mapIso (ActualResidualCompletedTarget.tensorCochainIso Λ X ηbar
      (ActualArithmeticDualSheaf.compactInput Λ X ηbar hΛ M))

end GaloisDerived

variable [Finite k]

/-- The SAME resolution lift after the specified completed Frobenius transport. -/
def profiniteIntCochain := ActualFiniteFieldTransport.cochain k Λ (galoisCochain Λ X ηbar K)

/-- Apply exact completed Frobenius scalar restriction to the actual lift. -/
def toNativeProfiniteInt : profiniteIntCochain Λ X ηbar K ⟶
    ActualResidualCompletedTarget.profiniteIntCochain Λ X ηbar K :=
  ((ActualFiniteFieldTransport.modules k Λ).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (toNative Λ X ηbar K)

/-- Scalar restriction is exact, so it preserves the specified quasi-isomorphism. -/
instance toNativeProfiniteInt_quasiIso : QuasiIso (toNativeProfiniteInt Λ X ηbar K) := by
  unfold toNativeProfiniteInt
  -- Local instance justification (defeq pin): expose the actual scalar restriction in Frobenius transport.
  letI : (ActualFiniteFieldTransport.modules k Λ).PreservesHomology :=
    inferInstanceAs ((ModuleCat.restrictScalars
      (ActualFiniteFieldTransport.ringEquiv k Λ).symm.toRingHom).PreservesHomology)
  -- Local instance justification (defeq pin): use the already proved quasi-isomorphism of this specified lift.
  letI : QuasiIso (toNative Λ X ηbar K) := toNative_quasiIso Λ X ηbar K
  exact HomologicalComplex.quasiIso_map_of_preservesHomology
    (toNative Λ X ηbar K) (ActualFiniteFieldTransport.modules k Λ)

variable [HasDerivedCategory (ModuleCat.{u + 1}
    (completedGroupRing Λ (ActualFiniteFieldTransport.profiniteInt.{u} : Type u)))]

/-- Localize the specified transported resolution lift. -/
def nativeDerivedIso : DerivedCategory.Q.obj (profiniteIntCochain Λ X ηbar K) ≅
    DerivedCategory.Q.obj (ActualResidualCompletedTarget.profiniteIntCochain Λ X ηbar K) :=
  asIso (DerivedCategory.Q.map (toNativeProfiniteInt Λ X ηbar K))

/-- Integrated with the existing finite inverse-Tate input and the actual
completed tensor target. This is the target-side bridge only: it does not
assert that geometric compact support is its source. -/
def finiteInputTensorIso (hΛ : IsUnit (Nat.card Λ : k))
    (M : (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory) :
    DerivedCategory.Q.obj (profiniteIntCochain Λ X ηbar
      (ActualArithmeticDualSheaf.compactInput Λ X ηbar hΛ M)) ≅
    ActualResidualCompletedTarget.derivedTensorTarget Λ X ηbar hΛ M :=
  nativeDerivedIso Λ X ηbar (ActualArithmeticDualSheaf.compactInput Λ X ηbar hΛ M) ≪≫
    ActualResidualCompletedTarget.derivedTensorIso Λ X ηbar hΛ M

end ActualCompletedDualResolution
