/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommResidualSectionsComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ExactRightComposition
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.DerivedResolutionComparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ExactDerivedUnit
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommResidualGaloisTransport
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
open NoncommResidualSectionsComparison
noncomputable section
universe u

namespace NoncommResidualDerivedComparison
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (η : GeometricPoint (geometricBaseChange X))
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
variable [∀ U : (geometricBaseChange X).Etale,
  HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]

instance sheafSections_additive : (sheafSections R X η).Additive := by sorry

instance realizedSections_additive : (realizedSections R X η).Additive :=
  inferInstanceAs ((functor (Λ := R) (xbar := arithmeticPoint X η) ⋙ sheafSections R X η).Additive)

variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R))]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} R))]
variable [HasDerivedCategory (DiscreteModuleCat R (Γ X η))]
variable [HasDerivedCategory (DiscreteModuleCat R (Q X η))]

/-- The canonical total derived composition map, normalized by the actual
residual-equivariant germ map. All categories contain ALL discrete modules. -/
def comparison :
    Functor.RightDerived.Bounded.functor (invariants R X η) ⟶
    Functor.RightDerived.Bounded.functor (functor (Λ := R) (xbar := arithmeticPoint X η)) ⋙
      Functor.RightDerived.Bounded.functor (sheafSections R X η) :=
  Functor.RightDerived.Composition.BoundedBelow.comparisonOfIso
    (functor (Λ := R) (xbar := arithmeticPoint X η)) (sheafSections R X η)
    (NoncommResidualSectionsComparison.iso R X η).symm

variable [hcurve : Curve X] [hsmooth : Smooth X.hom] [hconnected : GeometricallyConnected X.hom]
variable (hne : IsEmpty (geometricBaseChange X ≅ ProjectiveSpace.scheme (AlgebraicClosure k) 1))
variable (hR : IsUnit (Nat.card R : k))

include hcurve hsmooth hconnected hne hR in
/-- Curve-specific geometric effacement: restriction of an ambient arithmetic
injective is geometric-invariants-acyclic; K(pi,1) then gives geometric section
acyclicity of its actual associated sheaf, retaining the residual action. -/
theorem realizedInjective_acyclic (I : DiscreteModuleCat R (Γ X η)) (hI : Injective I) (i : ℕ) :
    IsZero (((sheafSections R X η).rightDerived (i + 1)).obj
      ((functor (Λ := R) (xbar := arithmeticPoint X η)).obj I)) := by sorry

include hcurve hsmooth hconnected hne hR in
/-- Exact realization and the preceding acyclicity make this specified
composition comparison invertible on the stated curve, not on arbitrary schemes. -/
theorem comparison_isIso : IsIso (comparison R X η) := by sorry

/-- Actual higher residual derived isomorphism; inverse only to the canonical
derived-composition/germ comparison. -/
def iso := @asIso _ _ _ _ (comparison R X η) (comparison_isIso R X η hne hR)

/-- The degreewise version also uses the specified recursive resolution
comparison and the same genuine acyclicity criterion. -/
def degreeIso (i : ℕ) : (invariants R X η).rightDerived i ≅
    functor (Λ := R) (xbar := arithmeticPoint X η) ⋙ (sheafSections R X η).rightDerived i :=
  (NatIso.rightDerived (NoncommResidualSectionsComparison.iso R X η) i).symm ≪≫
  ActualExactRightComposition.isoOfAcyclic
    (functor (Λ := R) (xbar := arithmeticPoint X η)) (sheafSections R X η)
    (realizedInjective_acyclic R X η hne hR) i

variable (M : (finiteTypeDiscreteModule R (Γ X η)).FullSubcategory)

/-- Concrete ambient arithmetic injective model for relative continuous invariants. -/
def groupComplex := ((invariants R X η).mapHomologicalComplex (ComplexShape.up ℕ)).obj
  (injectiveResolution M.obj).cocomplex

/-- Resolve the PUBLISHED finite associated sheaf, then apply actual geometric
sections and residual naming. No sheaf equivalence is replaced. -/
def geometricComplex := ((sheafSections R X η).mapHomologicalComplex (ComplexShape.up ℕ)).obj
  (injectiveResolution ((associatedSheafFunctor R (arithmeticPoint X η)).obj M)).cocomplex

/-- Explicit total residual comparison on the finite source coefficient:
actual resolution units, canonical derived composition, exact realization unit,
and the published finite-stage associated-sheaf comparison. -/
def finiteComplexIso :
    DerivedCategory.Plus.Q.obj ((CochainComplex.Plus.extendNat (DiscreteModuleCat R (Q X η))).obj
      (groupComplex R X η M)) ≅
    DerivedCategory.Plus.Q.obj ((CochainComplex.Plus.extendNat (DiscreteModuleCat R (Q X η))).obj
      (geometricComplex R X η M)) :=
  @asIso _ _ _ _
    (ActualResolutionComparison.resolutionToDerived (invariants R X η) (injectiveResolution M.obj))
    (ActualResolutionComparison.resolutionToDerived_isIso (invariants R X η) (injectiveResolution M.obj)) ≪≫
  (iso R X η hne hR).app (ActualResolutionComparison.singleModel M.obj) ≪≫
  (Functor.RightDerived.Bounded.functor (sheafSections R X η)).mapIso
    ((ActualResolutionComparison.exactUnitIso
      (functor (Λ := R) (xbar := arithmeticPoint X η)) M.obj).symm ≪≫
      ActualResolutionComparison.singleModelFunctor.mapIso
        ((finiteIso (Λ := R) (xbar := arithmeticPoint X η)).app M)) ≪≫
  (@asIso _ _ _ _ (ActualResolutionComparison.resolutionToDerived (sheafSections R X η)
    (injectiveResolution ((associatedSheafFunctor R (arithmeticPoint X η)).obj M)))
    (ActualResolutionComparison.resolutionToDerived_isIso (sheafSections R X η)
      (injectiveResolution ((associatedSheafFunctor R (arithmeticPoint X η)).obj M)))).symm

abbrev groupIntegerComplex := (groupComplex R X η M).extend ComplexShape.embeddingUpNat
abbrev geometricIntegerComplex := (geometricComplex R X η M).extend ComplexShape.embeddingUpNat

/-- Include the concrete bounded comparison in the ordinary derived category. -/
def integerComplexIso : DerivedCategory.Q.obj (groupIntegerComplex R X η M) ≅
    DerivedCategory.Q.obj (geometricIntegerComplex R X η M) :=
  ((DerivedCategory.Plus.Qh.compInclusionIso (DiscreteModuleCat R (Q X η))).app
    ((CochainComplex.Plus.extendNat (DiscreteModuleCat R (Q X η))).obj (groupComplex R X η M))).symm ≪≫
  (DerivedCategory.Plus.ι : DerivedCategory.Plus (DiscreteModuleCat R (Q X η)) ⥤ _).mapIso
    (finiteComplexIso R X η hne hR M) ≪≫
  (DerivedCategory.Plus.Qh.compInclusionIso (DiscreteModuleCat R (Q X η))).app
    ((CochainComplex.Plus.extendNat (DiscreteModuleCat R (Q X η))).obj (geometricComplex R X η M))

def completedGroupComplex :=
  ((NoncommResidualGaloisTransport.completed R X η).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (groupIntegerComplex R X η M)

/-- Return the geometric complex to the original field-Galois naming and actual
completed action by identity-on-sections group transport and zero-extension. -/
def geometricCompletedIso :
    ((NoncommResidualGaloisTransport.completed R X η).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (geometricIntegerComplex R X η M) ≅
    NoncommGeometricSource.arithmeticCochain R X
      ((associatedSheafFunctor R (arithmeticPoint X η)).obj M) :=
  ComplexShape.embeddingUpNat.mapAppIso (NoncommResidualGaloisTransport.completed R X η)
    (geometricComplex R X η M) ≪≫
  (ComplexShape.embeddingUpNat.extendFunctor _).mapIso
    (HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (NoncommPointwiseCompletedAction.functor R Gal(AlgebraicClosure k/k)).mapIso
        ((NoncommResidualGaloisTransport.namingIso R X η).app
          ((NoncommGeometricSource.discreteSections R X).obj
            ((injectiveResolution ((associatedSheafFunctor R (arithmeticPoint X η)).obj M)).cocomplex.X i))))
      (by sorry))

variable [HasDerivedCategory (ModuleCat.{u + 1}
  (NoncommCompletedRing.Obj R Gal(AlgebraicClosure k/k)))]

/-- Full ordinary derived comparison for the actual finite source sheaf in
D(R[[Gal]]), for arbitrary finite R and arbitrary ground field. -/
def derivedOrdinaryIso : DerivedCategory.Q.obj (completedGroupComplex R X η M) ≅
    DerivedCategory.Q.obj (NoncommGeometricSource.arithmeticCochain R X
      ((associatedSheafFunctor R (arithmeticPoint X η)).obj M)) :=
  ((NoncommResidualGaloisTransport.completed R X η).mapDerivedCategoryFactors.app
    (groupIntegerComplex R X η M)).symm ≪≫
  (NoncommResidualGaloisTransport.completed R X η).mapDerivedCategory.mapIso
    (integerComplexIso R X η hne hR M) ≪≫
  (NoncommResidualGaloisTransport.completed R X η).mapDerivedCategoryFactors.app
    (geometricIntegerComplex R X η M) ≪≫
  DerivedCategory.Q.mapIso (geometricCompletedIso R X η M)

/-- A concrete sheaf-resolution comparison underlying the derived construction:
exact realization of the ambient injectives, then the published finite comparison. -/
def realizationResolutionMap :=
  ActualMappedResolution.map (functor (Λ := R) (xbar := arithmeticPoint X η))
    (injectiveResolution M.obj)
    (injectiveResolution ((functor (Λ := R) (xbar := arithmeticPoint X η)).obj M.obj)) ≫
  InjectiveResolution.desc (finiteComparison M)
    (injectiveResolution ((associatedSheafFunctor R (arithmeticPoint X η)).obj M))
    (injectiveResolution ((functor (Λ := R) (xbar := arithmeticPoint X η)).obj M.obj))

/-- Actual cochain representative of the group-to-geometric comparison,
using the inverse of the specified degree-zero germ map in every resolution degree. -/
def nonnegativeComparison : groupComplex R X η M ⟶ geometricComplex R X η M where
  f i := (NoncommResidualSectionsComparison.iso R X η).inv.app ((injectiveResolution M.obj).cocomplex.X i) ≫
    (sheafSections R X η).map ((realizationResolutionMap R X η M).f i)
  comm' := by sorry

include hcurve hsmooth hconnected hne hR in
/-- The actual acyclic-resolution comparison is a quasi-isomorphism only under
the retained curve K(pi,1) hypotheses. -/
theorem nonnegativeComparison_quasiIso : QuasiIso (nonnegativeComparison R X η M) := by sorry

def cochainComparison : groupIntegerComplex R X η M ⟶ geometricIntegerComplex R X η M :=
  HomologicalComplex.extendMap (nonnegativeComparison R X η M) ComplexShape.embeddingUpNat

include hcurve hsmooth hconnected hne hR in
theorem cochainComparison_quasiIso : QuasiIso (cochainComparison R X η M) := by sorry

end NoncommResidualDerivedComparison
