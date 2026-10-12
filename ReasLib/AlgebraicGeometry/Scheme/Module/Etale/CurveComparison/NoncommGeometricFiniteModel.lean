/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommArithmeticDualSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteCurveComplexModel
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteCurveProjectiveModel
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FieldGeometricAdjunction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ResidualDirectImageSections

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace NoncommGeometricFiniteModel
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


variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Rᵐᵒᵖ),
    (smallEtalePullback f).op.HasLeftKanExtension F]
variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ))]

/-- Actual geometric sections of the arithmetic intrinsic dual resolution. -/
abbrev ordinary := NoncommGeometricSource.arithmeticDiscreteCochain Rᵐᵒᵖ X
  (NoncommArithmeticDualSheaf.intrinsic R X η M)

/-- The resolution was extended from nonnegative degrees. -/
instance ordinary_nonnegative : CochainComplex.IsStrictlyGE (ordinary R X η M) 0 := by sorry

variable [hcurve : Curve X] [hsmooth : Smooth X.hom]
variable [hconnected : GeometricallyConnected X.hom]

include hcurve hsmooth hconnected hR in
/-- Genuine curve finiteness for finite prime-to-characteristic local coefficients. -/
theorem ordinary_homology_finite (i : ℤ) : Finite ((ordinary R X η M).homology i).obj.V := by sorry

include hcurve hsmooth hconnected hR in
/-- The source curve, not an arbitrary scheme, gives the upper bound. -/
theorem ordinary_above_two (i : ℤ) (hi : 2 < i) :
    IsZero ((ordinary R X η M).homology i) := by sorry

/-- The actual finite invariant subcomplex of the canonical truncation. -/
abbrev finiteCochain := FiniteCurveComplexModel.finiteCochain Rᵐᵒᵖ Gal(AlgebraicClosure k/k)
  (ordinary R X η M)

/-- Inclusion of the chosen cycles/boundary lifts into the actual ordinary resolution. -/
def inclusion := FiniteCurveComplexModel.inclusion Rᵐᵒᵖ Gal(AlgebraicClosure k/k)
  (ordinary R X η M)

include hcurve hsmooth hconnected hR in
/-- The specified inclusion is a quasi-isomorphism under exactly the curve bound. -/
theorem inclusion_quasiIso : QuasiIso (inclusion R X η M) :=
  FiniteCurveComplexModel.inclusion_quasiIso Rᵐᵒᵖ Gal(AlgebraicClosure k/k)
    (ordinary R X η M) (ordinary_above_two R X η hR M)

include hcurve hsmooth hconnected hR in
/-- Finiteness is derived from actual geometric cohomology, not imposed as a new source assumption. -/
theorem finite_terms (i : ℤ) : Finite ((finiteCochain R X η M).X i).obj.V := by
  -- Local instance justification (proof-local temporary data): degree-zero curve cohomology is finite.
  letI : Finite ((ordinary R X η M).homology 0).obj.V := ordinary_homology_finite R X η hR M 0
  -- Local instance justification (proof-local temporary data): degree-one curve cohomology is finite.
  letI : Finite ((ordinary R X η M).homology 1).obj.V := ordinary_homology_finite R X η hR M 1
  -- Local instance justification (proof-local temporary data): degree-two curve cohomology is finite.
  letI : Finite ((ordinary R X η M).homology 2).obj.V := ordinary_homology_finite R X η hR M 2
  exact FiniteCurveComplexModel.finite_terms Rᵐᵒᵖ Gal(AlgebraicClosure k/k) (ordinary R X η M) i

/-- Actual finite-term coefficient-projective replacement of geometric ordinary
cohomology of the intrinsic RIGHT dual. Curve finiteness discharges the input classes. -/
def projectiveCochain :=
  -- Local instance justification (proof-local temporary data): curve H0 is finite.
  letI : Finite ((ordinary R X η M).homology 0).obj.V := ordinary_homology_finite R X η hR M 0
  -- Local instance justification (proof-local temporary data): curve H1 is finite.
  letI : Finite ((ordinary R X η M).homology 1).obj.V := ordinary_homology_finite R X η hR M 1
  -- Local instance justification (proof-local temporary data): curve H2 is finite.
  letI : Finite ((ordinary R X η M).homology 2).obj.V := ordinary_homology_finite R X η hR M 2
  FiniteCurveProjectiveModel.complex Rᵐᵒᵖ Gal(AlgebraicClosure k/k) (ordinary R X η M)

/-- Specified comparison into the actual geometric sections complex, retaining its Galois action. -/
def projectiveMap : projectiveCochain R X η hR M ⟶ ordinary R X η M :=
  -- Local instance justification (proof-local temporary data): curve H0 is finite.
  letI : Finite ((ordinary R X η M).homology 0).obj.V := ordinary_homology_finite R X η hR M 0
  -- Local instance justification (proof-local temporary data): curve H1 is finite.
  letI : Finite ((ordinary R X η M).homology 1).obj.V := ordinary_homology_finite R X η hR M 1
  -- Local instance justification (proof-local temporary data): curve H2 is finite.
  letI : Finite ((ordinary R X η M).homology 2).obj.V := ordinary_homology_finite R X η hR M 2
  FiniteCurveProjectiveModel.toOriginal Rᵐᵒᵖ Gal(AlgebraicClosure k/k) (ordinary R X η M)

theorem projectiveMap_quasiIso : QuasiIso (projectiveMap R X η hR M) := by
  -- Local instance justification (proof-local temporary data): curve H0 is finite.
  letI : Finite ((ordinary R X η M).homology 0).obj.V := ordinary_homology_finite R X η hR M 0
  -- Local instance justification (proof-local temporary data): curve H1 is finite.
  letI : Finite ((ordinary R X η M).homology 1).obj.V := ordinary_homology_finite R X η hR M 1
  -- Local instance justification (proof-local temporary data): curve H2 is finite.
  letI : Finite ((ordinary R X η M).homology 2).obj.V := ordinary_homology_finite R X η hR M 2
  exact FiniteCurveProjectiveModel.toOriginal_quasiIso Rᵐᵒᵖ Gal(AlgebraicClosure k/k)
    (ordinary R X η M) (ordinary_above_two R X η hR M)

/-- Pull the finite-term Galois replacement back to X and apply the actual
section counit into the intrinsic dual's arithmetic injective resolution.
This is a concrete sheaf cochain arrow, before any derived localization. -/
def arithmeticSheafMap :=
  FieldGeometricAdjunction.adjointExtendedMap Rᵐᵒᵖ X
    (injectiveResolution (NoncommArithmeticDualSheaf.intrinsic R X η M)).cocomplex
    (projectiveMap R X η hR M)

variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)

/-- The arithmetic injective resolution on the open curve, extended in degree only. -/
abbrev dualResolution :=
  (injectiveResolution (NoncommArithmeticDualSheaf.intrinsic R X η M)).cocomplex.extend
    ComplexShape.embeddingUpNat

/-- Direct image of that resolution represents Rj_* of the intrinsic right
dual. It is NOT called a resolution of the ordinary j_* sheaf. -/
def compactDualComplex :=
  ((ResidualDirectImageSections.pushforward Rᵐᵒᵖ P.obj.hom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (dualResolution R X η M)

/-- Actual section/zero-extension identification, followed by the inverse
of the direct-image section counit comparison. -/
def ordinaryToCompactDual : ordinary R X η M ⟶
    ((NoncommGeometricSource.discreteSections Rᵐᵒᵖ P.obj.right).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (compactDualComplex R X η M P) :=
  FieldGeometricAdjunction.sectionsExtensionMap Rᵐᵒᵖ X
    (injectiveResolution (NoncommArithmeticDualSheaf.intrinsic R X η M)).cocomplex ≫
  (ResidualDirectImageSections.cochainIso Rᵐᵒᵖ P.obj.hom (dualResolution R X η M)).inv

/-- The connected global arithmetic arrow on the compactification, ready for
comparison with internal Hom. Every map is defined before derived localization. -/
def compactArithmeticSheafMap :=
  FieldGeometricAdjunction.adjointCochainMap Rᵐᵒᵖ P.obj.right
    (projectiveMap R X η hR M ≫ ordinaryToCompactDual R X η M P)

end NoncommGeometricFiniteModel
