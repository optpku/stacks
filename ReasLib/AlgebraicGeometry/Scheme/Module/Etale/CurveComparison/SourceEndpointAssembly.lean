/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LambdaEndpointAssembly
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CompactRootsPullback

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
noncomputable section
universe u

namespace ActualSourceAssembly
section Geometry
variable {k : Type u} [Field k]

/-- Only geometric compactification data are chosen; no comparison map or
cohomology object is part of this record. -/
structure Completion (Z : SchemeOverField k) where
  curve : SchemeOverField k
  j : Z ⟶ curve
  isCurve : Curve curve
  regular : Scheme.Regular curve.left
  projective : Projective curve.hom
  smooth : Smooth curve.hom
  isOpen : IsOpenImmersion j.left

variable (Z : SchemeOverField k)
variable [hcurve : Curve Z] [hregular : Scheme.Regular Z.left] [hperfect : PerfectField k]

include hcurve hregular hperfect in
theorem completion_nonempty : Nonempty (Completion Z) := by
  obtain ⟨C, j, hj, hfac, hc, hr, hp, hs, _⟩ :=
    Curve.exists_smoothProjectiveCompactification_of_regular_of_perfectField Z
  exact ⟨⟨C, Over.homMk j hfac, hc, hr, hp, hs, hj⟩⟩

def completion : Completion Z := (completion_nonempty Z).some

instance completion_curve : Curve (completion Z).curve := (completion Z).isCurve
instance completion_regular : Scheme.Regular (completion Z).curve.left := (completion Z).regular
instance completion_projective : Projective (completion Z).curve.hom := (completion Z).projective
instance completion_smooth : Smooth (completion Z).curve.hom := (completion Z).smooth
instance completion_open : IsOpenImmersion (completion Z).j.left := (completion Z).isOpen

end Geometry

variable {k : Type u} [Field k]

abbrev Xgeom (X : SchemeOverField k) := ActualFiniteDualComparison.geometricCurve X

/-- These hypotheses must be explicit instance binders: `include` alone does
not retain section assumptions in an instance whose proof is deferred. -/
instance geometricCurve (X : SchemeOverField k) [Curve X] [Smooth X.hom]
    [GeometricallyConnected X.hom] : Curve (Xgeom X) := sorry
instance geometricRegular (X : SchemeOverField k) [Smooth X.hom] :
    Scheme.Regular (Xgeom X).left := sorry

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (X : SchemeOverField k) [hcurve : Curve X] [hsmooth : Smooth X.hom]
variable [hconnected : GeometricallyConnected X.hom]
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (ηbar : GeometricPoint (geometricBaseChange X))
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)

def geometricInterior : Xgeom X ⟶ ActualFiniteDualComparison.geometricCurve P.obj.right :=
  Over.homMk (ActualGeometricCompactSupport.interior X P) (by sorry)

instance geometricInterior_open : IsOpenImmersion (geometricInterior X P).left :=
  ActualGeometricCompactSupport.interior_open X P

instance geometricInterior_qc : QuasiCompact (geometricInterior X P).left := sorry
instance geometricAmbient_proper : IsProper (ActualFiniteDualComparison.geometricCurve P.obj.right).hom := sorry

/-- The arbitrary source compactification base-changed to the algebraic closure. -/
def geometricCompactification : Compactification.Of (Spec (CommRingCat.of (AlgebraicClosure k))) (Xgeom X) :=
  Compactification.Of.mk _ (ActualFiniteDualComparison.geometricCurve P.obj.right) (geometricInterior X P)

variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ Y : Scheme.{u}, ∀ U : Y.Etale,
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology
    (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))]
variable [∀ Y : Scheme.{u}, ∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U)
    (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))]
variable [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ Y : Scheme.{u}, HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]
variable [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose (ActualFiniteCoefficient.modules Λ)]
variable [∀ Y : Scheme.{u}, Y.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ))) AddCommGrpCat.{u + 1})]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}),
    (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ), (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
    (F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}), (etaleRestriction j).op.HasLeftKanExtension F]
variable (M : (finiteTypeDiscreteModule Λ
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X ηbar)))).FullSubcategory)

/-- The finite associated-sheaf base-change is the existing actual germ and
finite-colimit comparison, now exposed before applying cohomology. -/
def sourceSheafIso :
    (AmbientGeometry.modulePullback Λ (geometricToArithmeticHom X)).obj
      ((associatedSheafFunctor Λ (arithmeticPoint X ηbar)).obj M) ≅
    ActualFiniteDualComparison.sourceSheaf Λ X ηbar (ActualArithmeticDualSheaf.geometricInput Λ X ηbar M) :=
  ((AmbientGeometry.modulePullback Λ (geometricToArithmeticHom X)).mapIso
    ((finiteIso (Λ := Λ) (xbar := arithmeticPoint X ηbar)).app M)).symm ≪≫
  baseChangeIso Λ (geometricToArithmeticHom X) ηbar M.obj ≪≫
  (functor (Λ := Λ) (xbar := ηbar)).mapIso (AmbientCurve.finiteRestrictionModelIso Λ X ηbar M) ≪≫
  (finiteIso (Λ := Λ) (xbar := ηbar)).app (ActualArithmeticDualSheaf.geometricInput Λ X ηbar M)

abbrev additiveSource := (ActualSiteExt.moduleForget (geometricBaseChange X) Λ).obj
  (ActualFiniteDualComparison.sourceSheaf Λ X ηbar (ActualArithmeticDualSheaf.geometricInput Λ X ηbar M))

/-- Source Hc is carried to the additive extension on its geometric compactification
by the base-change mate, finite associated-sheaf map, and scalar-forgetting mate. -/
def sourceGeometricEquiv (a : ℕ) :
    geometricModuleEtaleHqCompactSupport X P
      ((associatedSheafFunctor Λ (arithmeticPoint X ηbar)).obj M) a ≃+
    ((etaleExtensionByZero (ActualGeometricCompactSupport.interior X P) AddCommGrpCat.{u + 1}).obj
      (additiveSource Λ X ηbar M)).H a :=
  (ActualGeometricCompactSupport.cohomologyIso X P Λ
    ((associatedSheafFunctor Λ (arithmeticPoint X ηbar)).obj M) a).toLinearEquiv.toAddEquiv |>.trans
  ((Sheaf.functorH (geometricBaseChange P.obj.right).smallEtaleTopology a).mapIso
    ((ActualSiteExt.moduleForget (geometricBaseChange P.obj.right) Λ).mapIso
      ((etaleExtensionByZero (ActualGeometricCompactSupport.interior X P) (ModuleCat.{u + 1} Λ)).mapIso
        (sourceSheafIso Λ X ηbar M)) ≪≫
      (ActualLambdaEndpoint.extensionForgetIso Λ (ActualGeometricCompactSupport.interior X P)
        (ActualFiniteDualComparison.sourceSheaf Λ X ηbar
          (ActualArithmeticDualSheaf.geometricInput Λ X ηbar M))).symm)).addCommGroupIsoToAddEquiv

/-- Finite Lambda annihilates every section, including sections on infinite etale objects. -/
theorem source_torsion (V : (geometricBaseChange X).Etaleᵒᵖ)
    (s : (additiveSource Λ X ηbar M).obj.obj V) : IsOfFinAddOrder s := sorry

/-- The exact CURRENT source endpoint maps to the chosen regular projective
curve via the specified geometric refinement and its actual Ext pullback. -/
def sourceRegularEquiv (a : ℕ) :=
  (sourceGeometricEquiv Λ X ηbar P M a).trans
    (ActualCurveRefinement.cohomologyEquiv (Xgeom X) (completion (Xgeom X)).curve
      (completion (Xgeom X)).j (geometricCompactification X P)
      (additiveSource Λ X ηbar M) (source_torsion Λ X ηbar M) a)

end ActualSourceAssembly
