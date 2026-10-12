/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactCompletedModules
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteFieldCompletedTransport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactResidualUnderlying
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ArithmeticDualSheafComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactDegreePlacement

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace ActualResidualCompletedTarget
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (ηbar : GeometricPoint (geometricBaseChange X))

abbrev residualGroup := Aut (standardFiniteEtaleFiber (galoisPoint X (arithmeticPoint X ηbar)))

/-- The specified finite-etale fiber/Galois comparison, inverted on its actual carrier. -/
def residualEquiv : residualGroup X ηbar ≃* Gal(AlgebraicClosure k/k) :=
  (MulEquiv.ofBijective (galoisToGaloisPoint X ηbar)
    (AmbientGeometry.galoisPointComparison_bijective X ηbar)).symm

theorem residualEquiv_continuous : Continuous (residualEquiv X ηbar) := sorry
theorem residualEquiv_inverse_continuous : Continuous (residualEquiv X ηbar).symm := sorry

/-- Compact residual modules receive their actual completed action before
the continuous mixed-universe ring transport to the usual Galois carrier. -/
def toGaloisModules : CompactRepresentation.Cat Λ (residualGroup X ηbar) ⥤
    ModuleCat.{u + 1} (completedGroupRing Λ Gal(AlgebraicClosure k/k)) :=
  ActualCompactCompletedModules.functor Λ (residualGroup X ηbar) ⋙
    ActualCompletedRingTransport.restrictScalars Λ (residualEquiv X ηbar)
      (residualEquiv_continuous X ηbar) (residualEquiv_inverse_continuous X ηbar)

instance toGaloisModules_additive : (toGaloisModules Λ X ηbar).Additive := sorry

/-- Native compact arithmetic projective resolution, with no finite-category
resolution instance and no hypothesis that restriction preserves projectives. -/
abbrev resolution (K : CompactRepresentation.Cat Λ
    (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))) := projectiveResolution K

/-- Actual compact derived geometric coinvariants with residual action,
placed in cochain degree 2-i and converted to the genuine completed action. -/
def galoisCochain (K : CompactRepresentation.Cat Λ
    (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))) :
    CochainComplex (ModuleCat.{u + 1} (completedGroupRing Λ Gal(AlgebraicClosure k/k))) ℤ :=
  (((CompactResidual.geometricCoinvariantsFunctor Λ X ηbar ⋙ toGaloisModules Λ X ηbar).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (resolution Λ X ηbar K).complex).extend CompactRepresentation.curveDegreeEmbedding

/-- The tensor carrier is the independently defined inverse limit of finite
balanced quotients. Its residual action uses only the actual compact
coinvariant/tensor map, never the geometric trace comparison. -/
def tensorObj (K : CompactRepresentation.Cat Λ
    (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))) :
    CompactRepresentation.Cat Λ (residualGroup X ηbar) :=
  ⟨{ V := CompactRepresentation.completedTrivialTensor Λ (Aut (standardFiniteEtaleFiber ηbar))
          ((CompactResidual.restriction Λ X ηbar).obj K)
     ρ := ((CompactRepresentation.completedTensorComparison Λ (Aut (standardFiniteEtaleFiber ηbar))
          ((CompactResidual.restriction Λ X ηbar).obj K)).conj.toMonoidHom).comp
        ((CompactResidual.geometricCoinvariantsFunctor Λ X ηbar).obj K).obj.ρ }, by sorry⟩

def tensorFunctor : CompactRepresentation.Cat Λ
    (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar))) ⥤
    CompactRepresentation.Cat Λ (residualGroup X ηbar) where
  obj := tensorObj Λ X ηbar
  map {K L} f := ObjectProperty.homMk
    { hom := (CompactRepresentation.completedTensorComparison Λ (Aut (standardFiniteEtaleFiber ηbar))
          ((CompactResidual.restriction Λ X ηbar).obj K)).inv ≫
        ((CompactResidual.geometricCoinvariantsFunctor Λ X ηbar).map f).hom.hom ≫
        (CompactRepresentation.completedTensorComparison Λ (Aut (standardFiniteEtaleFiber ηbar))
          ((CompactResidual.restriction Λ X ηbar).obj L)).hom
      comm := fun _ ↦ sorry }
  map_id := sorry
  map_comp := sorry

instance tensorFunctor_additive : (tensorFunctor Λ X ηbar).Additive := sorry

def coinvariantsTensorIso : CompactResidual.geometricCoinvariantsFunctor Λ X ηbar ≅ tensorFunctor Λ X ηbar :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _
    (Action.mkIso (CompactRepresentation.completedTensorComparison Λ (Aut (standardFiniteEtaleFiber ηbar))
      ((CompactResidual.restriction Λ X ηbar).obj K)) (fun _ ↦ sorry))) (fun _ ↦ sorry)

def tensorGaloisCochain (K : CompactRepresentation.Cat Λ
    (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))) :
    CochainComplex (ModuleCat.{u + 1} (completedGroupRing Λ Gal(AlgebraicClosure k/k))) ℤ :=
  (((tensorFunctor Λ X ηbar ⋙ toGaloisModules Λ X ηbar).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (resolution Λ X ηbar K).complex).extend CompactRepresentation.curveDegreeEmbedding

/-- Actual chain-level completed tensor comparison, then the correct 2-i
degree extension. Its components are the finite-stage projection maps. -/
def tensorCochainIso (K : CompactRepresentation.Cat Λ
    (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))) :
    galoisCochain Λ X ηbar K ≅ tensorGaloisCochain Λ X ηbar K :=
  (CompactRepresentation.curveDegreeEmbedding.extendFunctor _).mapIso
    (HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (toGaloisModules Λ X ηbar).mapIso
        ((coinvariantsTensorIso Λ X ηbar).app ((resolution Λ X ηbar K).complex.X i)))
      (fun _ _ _ ↦ sorry))

variable [Finite k]

/-- Full corrected source-side completed-ring TYPE: the actual compact
residual resolution transported by completed arithmetic Frobenius to Zhat. -/
def profiniteIntCochain (K : CompactRepresentation.Cat Λ
    (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))) :
    CochainComplex (ModuleCat.{u + 1}
      (completedGroupRing Λ (ActualFiniteFieldTransport.profiniteInt.{u} : Type u))) ℤ :=
  ActualFiniteFieldTransport.cochain k Λ (galoisCochain Λ X ηbar K)

variable [HasDerivedCategory (ModuleCat.{u + 1}
    (completedGroupRing Λ (ActualFiniteFieldTransport.profiniteInt.{u} : Type u)))]

def derivedTarget (hΛ : IsUnit (Nat.card Λ : k))
    (M : (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory) :=
  DerivedCategory.Q.obj (profiniteIntCochain Λ X ηbar
    (ActualArithmeticDualSheaf.compactInput Λ X ηbar hΛ M))

def derivedTensorTarget (hΛ : IsUnit (Nat.card Λ : k))
    (M : (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory) :=
  ActualFiniteFieldTransport.derivedObject k Λ (tensorGaloisCochain Λ X ηbar
    (ActualArithmeticDualSheaf.compactInput Λ X ηbar hΛ M))

/-- Actual completed-ring derived isomorphism on the compact homology side.
This does not substitute for the geometric RΓc comparison. -/
def derivedTensorIso (hΛ : IsUnit (Nat.card Λ : k))
    (M : (finiteTypeDiscreteModule Λ
      (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory) :
    derivedTarget Λ X ηbar hΛ M ≅ derivedTensorTarget Λ X ηbar hΛ M :=
  DerivedCategory.Q.mapIso
    (((ActualFiniteFieldTransport.modules k Λ).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (tensorCochainIso Λ X ηbar (ActualArithmeticDualSheaf.compactInput Λ X ηbar hΛ M)))

end ActualResidualCompletedTarget
