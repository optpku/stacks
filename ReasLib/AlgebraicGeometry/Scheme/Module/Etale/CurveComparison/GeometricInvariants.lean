module

public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.DerivedInvariants
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocallyConstantPullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.Forward

/-!
# Ambient geometric invariants and cohomology

Restrict arithmetic representations to the geometric fundamental group and derive
invariants on all discrete continuous modules. Finite-type inputs are included
after taking the right derived functor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Action.ModuleCat
open CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.Ambient

variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (ηbar : GeometricPoint (geometricBaseChange X))

/-- Restrict an arithmetic continuous representation to geometric π₁. -/
def restriction :
    DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar))) ⥤
      DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber ηbar)) :=
  discreteModuleRes (geometricToArithmetic X ηbar).hom

/-- Geometric invariants on all arithmetic continuous representations. -/
def invariants :
    DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar))) ⥤
      ModuleCat.{u + 1} Λ :=
  restriction Λ X ηbar ⋙
    CategoryTheory.Action.ModuleCat.DiscreteModuleCat.fixedPointsFunctor Λ (Aut (GeometricPoint.finiteFiber ηbar))

/-- Continuous geometric cohomology, derived before imposing finite input. -/
def cohomology (i : ℕ) :
    DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar))) ⥤
      ModuleCat.{u + 1} Λ :=
  restriction Λ X ηbar ⋙
    CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyFunctor Λ (Aut (GeometricPoint.finiteFiber ηbar)) i

/-- The canonical degree-zero isomorphism is whiskering of the ambient derived unit. -/
def zeroIso : cohomology Λ X ηbar 0 ≅ invariants Λ X ηbar :=
  isoWhiskerLeft (restriction Λ X ηbar)
    (CategoryTheory.Action.ModuleCat.DiscreteModuleCat.derivedCohomologyZeroIso Λ (Aut (GeometricPoint.finiteFiber ηbar)))

/-- Finite inputs are included only after the ambient right derived functor exists. -/
def finiteCohomology (i : ℕ) :
    (finiteTypeDiscreteModule Λ
      (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory ⥤
        ModuleCat.{u + 1} Λ :=
  (finiteTypeDiscreteModule Λ
      (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).ι ⋙ cohomology Λ X ηbar i

/-- The inclusion of finite inputs preserves the specified degree-zero comparison. -/
def finiteZeroIso : finiteCohomology Λ X ηbar 0 ≅
    (finiteTypeDiscreteModule Λ
      (Aut (GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).ι ⋙ invariants Λ X ηbar :=
  isoWhiskerLeft _ (zeroIso Λ X ηbar)

end AlgebraicGeometry.SchemeOverField.Ambient
