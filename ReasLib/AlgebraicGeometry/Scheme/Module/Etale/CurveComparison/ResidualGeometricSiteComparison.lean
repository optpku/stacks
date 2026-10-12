/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGeometricSource
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricSheafCohomologyAction
public import ReasLib.Algebra.Homology.HomologicalComplex.PreservesHomology

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

/- Central trace-coefficient comparison over an arbitrary field. The central
ring A is commutative; this does not impose commutativity on the original R. -/
namespace ResidualGeometricSiteComparison
variable {k : Type u} [Field k]
variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} A)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A),
    (smallEtalePullback f).op.HasLeftKanExtension F]
variable (X : SchemeOverField k) [CompactSpace X.left] [QuasiSeparatedSpace X.left]

/-- Forget only the specified Galois action, retaining the coefficient module. -/
def forget : DiscreteModuleCat A Gal(AlgebraicClosure k/k) ⥤ ModuleCat.{u + 1} A :=
  (openStabilizer A Gal(AlgebraicClosure k/k)).ι ⋙
    Action.forget (ModuleCat.{u + 1} A) Gal(AlgebraicClosure k/k)

instance forget_additive : (forget (k := k) A).Additive := by sorry
instance forget_preservesHomology : (forget (k := k) A).PreservesHomology := by sorry

/-- Identity on actual geometric sections, before deriving either route. -/
def sectionsIso : NoncommGeometricSource.discreteSections A X ⋙ forget (k := k) A ≅
    AmbientGeometry.geometricSheafSectionsAction A X ⋙
      Action.forget (ModuleCat.{u + 1} A) Gal(AlgebraicClosure k/k) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by sorry)

variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} A))]
variable (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- The two actual resolution complexes agree by their section maps and the
canonical functor/zero-extension compositor. -/
def cochainIso :
    ((forget (k := k) A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (NoncommGeometricSource.arithmeticDiscreteCochain A X F) ≅
    (((AmbientGeometry.geometricSheafSectionsAction A X ⋙
      Action.forget (ModuleCat.{u + 1} A) Gal(AlgebraicClosure k/k)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex).extend
          ComplexShape.embeddingUpNat :=
  ComplexShape.embeddingUpNat.mapAppIso (forget (k := k) A)
    (((NoncommGeometricSource.discreteSections A X).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex) ≪≫
  (ComplexShape.embeddingUpNat.extendFunctor _).mapIso
    (HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ (sectionsIso A X).app ((injectiveResolution F).cocomplex.X i)) (by sorry))

/-- Homology comparison by exact forgetting, extension, and actual injective
resolution classes; no group-cohomology isomorphism enters this definition. -/
def derivedHomologyIso (n : ℕ) :
    (forget (k := k) A).obj ((NoncommGeometricSource.arithmeticDiscreteCochain A X F).homology (n : ℤ)) ≅
    ((AmbientGeometry.geometricSheafDerivedAction A X n).obj F).V :=
  ((NoncommGeometricSource.arithmeticDiscreteCochain A X F).mapHomologyIso (forget (k := k) A) (n : ℤ)).symm ≪≫
  (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) (n : ℤ)).mapIso (cochainIso A X F) ≪≫
  (((AmbientGeometry.geometricSheafSectionsAction A X ⋙
    Action.forget (ModuleCat.{u + 1} A) Gal(AlgebraicClosure k/k)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (injectiveResolution F).cocomplex).extendHomologyIso
        ComplexShape.embeddingUpNat rfl ≪≫
  ((injectiveResolution F).isoRightDerivedObj
    (AmbientGeometry.geometricSheafSectionsAction A X ⋙
      Action.forget (ModuleCat.{u + 1} A) Gal(AlgebraicClosure k/k)) n).symm ≪≫
  (Functor.RightDerived.postcompIso (AmbientGeometry.geometricSheafSectionsAction A X)
    (Action.forget (ModuleCat.{u + 1} A) Gal(AlgebraicClosure k/k)) n).app F

variable [EnoughInjectives (Sheaf (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} A))]
variable [HasSheafify (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [EnoughInjectives (Sheaf (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [(geometricBaseChange X).smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})]

/-- Actual site-Ext endpoint used to read the normalized roots trace. -/
def siteHomologyIso (n : ℕ) :
    (forget (k := k) A).obj ((NoncommGeometricSource.arithmeticDiscreteCochain A X F).homology (n : ℤ)) ≅
    geometricModuleEtaleHq X F n :=
  derivedHomologyIso A X F n ≪≫ (AmbientGeometry.geometricSheafDerivedSiteIso A X n).app F

end ResidualGeometricSiteComparison
