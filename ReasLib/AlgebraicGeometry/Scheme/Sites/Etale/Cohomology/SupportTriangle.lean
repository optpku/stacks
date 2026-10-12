/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.SupportFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pretriangulated
open ComplexShape ComplexShape.Embedding

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.Support

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The augmentation of an injective resolution after restriction to the open complement. -/
def restrictedAugmentation :
    (CochainComplex.single₀ (Sheaf (closedImmersionComplement i).toScheme.smallEtaleTopology
      AddCommGrpCat.{u + 1})).obj ((Abelian.inverseImage (closedImmersionComplement i).ι).obj F) ⟶
    ((Abelian.inverseImage (closedImmersionComplement i).ι).mapHomologicalComplex (.up ℕ)).obj
      (injectiveResolution F).cocomplex :=
  (HomologicalComplex.singleMapHomologicalComplex
      (Abelian.inverseImage (closedImmersionComplement i).ι) (.up ℕ) 0).inv.app F ≫
    ((Abelian.inverseImage (closedImmersionComplement i).ι).mapHomologicalComplex (.up ℕ)).map
      (injectiveResolution F).ι

/-- Restriction of the augmentation to the open complement is a quasi-isomorphism. -/
instance restrictedAugmentation_quasiIso : QuasiIso (restrictedAugmentation i F) := sorry

/-- An ambient injective resolution restricts to an injective resolution on the complement. -/
def restrictedResolution :
    InjectiveResolution ((Abelian.inverseImage (closedImmersionComplement i).ι).obj F) where
  cocomplex := ((Abelian.inverseImage (closedImmersionComplement i).ι).mapHomologicalComplex
    (.up ℕ)).obj (injectiveResolution F).cocomplex
  injective degree := inverseImage_injective i ((injectiveResolution F).cocomplex.X degree)
  ι := restrictedAugmentation i F
  quasiIso := restrictedAugmentation_quasiIso i F

/-- The resolution-level support inclusion and complementary restriction form a short complex,
extended by zero from nonnegative to integer degrees. -/
def resolutionSequence :
    ShortComplex (CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :=
  (ShortComplex.mk
    ((NatTrans.mapHomologicalComplex (inclusion i) (.up ℕ)).app
      (injectiveResolution F).cocomplex)
    ((NatTrans.mapHomologicalComplex
      (Abelian.adjunction (closedImmersionComplement i).ι).unit (.up ℕ)).app
      (injectiveResolution F).cocomplex)
    ((congrArg (fun transformation => transformation.app (injectiveResolution F).cocomplex)
      (NatTrans.mapHomologicalComplex_comp (.up ℕ) (inclusion i)
        (Abelian.adjunction (closedImmersionComplement i).ι).unit)).symm.trans
      (congrArg (fun transformation =>
        (NatTrans.mapHomologicalComplex transformation (.up ℕ)).app
          (injectiveResolution F).cocomplex) (inclusion_comp_unit i)))).map
    (embeddingUpNat.extendFunctor _)

/-- The supported injective-resolution sequence is short exact. -/
theorem resolutionSequence_shortExact : (resolutionSequence i F).ShortExact := sorry

/-- The localized injective resolution is canonically isomorphic to the sheaf in degree zero. -/
def resolutionIso : DerivedCategory.Q.obj (resolutionSequence i F).X₂ ≅
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F :=
  (asIso (DerivedCategory.Q.map
    (HomologicalComplex.extendMap (injectiveResolution F).ι embeddingUpNat))).symm ≪≫
    DerivedCategory.Q.mapIso
      (HomologicalComplex.extendSingleIso embeddingUpNat F 0 0 rfl)

/-- Derived sections with closed support, pushed forward to the ambient scheme, are computed
by the supported injective resolution. -/
def derivedSupport : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  DerivedCategory.Q.obj (resolutionSequence i F).X₁

/-- The derived direct image from the complement is computed by its canonical injective
resolution of the restricted sheaf. -/
def derivedOpen : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  DerivedCategory.Q.obj
    ((((Abelian.directImage (closedImmersionComplement i).ι).mapHomologicalComplex (.up ℕ)).obj
      (injectiveResolution ((Abelian.inverseImage (closedImmersionComplement i).ι).obj F)).cocomplex).extend
      embeddingUpNat)

/-- Comparison of restricted and canonical injective resolutions identifies the open term. -/
def openResolutionIso : DerivedCategory.Q.obj (resolutionSequence i F).X₃ ≅ derivedOpen i F :=
  let directImage := Abelian.directImage (closedImmersionComplement i).ι
  let restricted := (directImage.mapHomologicalComplex (.up ℕ)).obj
    (restrictedResolution i F).cocomplex
  let canonical := (directImage.mapHomologicalComplex (.up ℕ)).obj
    (injectiveResolution ((Abelian.inverseImage (closedImmersionComplement i).ι).obj F)).cocomplex
  (DerivedCategory.quotientCompQhIso
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})).symm.app
      (restricted.extend embeddingUpNat) ≪≫
    DerivedCategory.Qh.mapIso
      ((embeddingUpNat.extendHomotopyFunctorFactors _).symm.app restricted) ≪≫
    DerivedCategory.Qh.mapIso
      ((embeddingUpNat.extendHomotopyFunctor _).mapIso
        (HomotopyCategory.isoOfHomotopyEquiv
          ((Abelian.directImage (closedImmersionComplement i).ι).mapHomotopyEquiv
            ((restrictedResolution i F).homotopyEquiv
              (injectiveResolution ((Abelian.inverseImage (closedImmersionComplement i).ι).obj F)))))) ≪≫
    DerivedCategory.Qh.mapIso
      ((embeddingUpNat.extendHomotopyFunctorFactors _).app canonical) ≪≫
    (DerivedCategory.quotientCompQhIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})).app (canonical.extend embeddingUpNat)

/-- The support morphism is the localized resolution inclusion transported to the single sheaf. -/
def supportMap : derivedSupport i F ⟶
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F :=
  DerivedCategory.Q.map (resolutionSequence i F).f ≫ (resolutionIso i F).hom

/-- The restriction morphism is the localized complementary unit transported to canonical terms. -/
def restrictionUnitMap :
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F ⟶
      derivedOpen i F :=
  (resolutionIso i F).inv ≫ DerivedCategory.Q.map (resolutionSequence i F).g ≫
    (openResolutionIso i F).hom

/-- The support inclusion followed by complementary restriction vanishes. -/
theorem supportMap_comp_restrictionUnit :
    supportMap i F ≫ restrictionUnitMap i F = 0 := sorry

/-- The boundary morphism is the connecting morphism of the supported resolution sequence. -/
def boundaryMap : derivedOpen i F ⟶ (derivedSupport i F)⟦(1 : ℤ)⟧ :=
  (openResolutionIso i F).inv ≫
    (DerivedCategory.triangleOfSES (resolutionSequence_shortExact i F)).mor₃

/-- The support triangle relates derived support, the ambient sheaf, and the derived open image. -/
def triangle : Triangle (DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  Triangle.mk (supportMap i F) (restrictionUnitMap i F) (boundaryMap i F)

/-- The support map is the localized inclusion followed by the resolution comparison. -/
theorem supportMap_apply : supportMap i F =
    DerivedCategory.Q.map (resolutionSequence i F).f ≫ (resolutionIso i F).hom := sorry

/-- The restriction map is the localized restriction unit transported by resolution comparisons. -/
theorem restrictionUnitMap_apply : restrictionUnitMap i F =
    (resolutionIso i F).inv ≫ DerivedCategory.Q.map (resolutionSequence i F).g ≫
      (openResolutionIso i F).hom := sorry

/-- The support triangle for a closed immersion and its open complement is distinguished. -/
theorem triangle_distinguished : triangle i F ∈ distinguishedTriangles := sorry

end AlgebraicGeometry.Scheme.Etale.Support
