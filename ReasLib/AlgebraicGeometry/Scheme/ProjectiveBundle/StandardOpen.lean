/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra.QuotientChart
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.OpenRestriction
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Presentation

/-!
# Standard-open coordinates for symmetric projective bundles

A standard-open factorization records an arbitrary affine refinement of a
test scheme, an affine open in the base-changed projective bundle, and
symmetric-algebra coordinates identifying the restricted section with the
augmentation.  The associated conormal morphism is constructed from the
induced map on augmentation ideals.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation

variable {X P : Scheme.{u}} {ℰ : X.Modules} [ℰ.IsQuasicoherent]
variable {π : P ⟶ X}

/-- The basic open determined by an element in an explicit affine relative-Proj model. -/
def relativeProjBasicOpen (D : Scheme.Hom.AbsoluteProjModel)
    (a : D.ring) : D.proj.Opens :=
  @AlgebraicGeometry.Proj.basicOpen D.grade D.ring D.ring.commRing
    D.gradeSetLike D.gradeAddSubgroupClass D.grading D.grading_inst a

/-- The degree-zero homogeneous-localization ring of an explicit affine relative-Proj model. -/
noncomputable def relativeProjAwayRing (D : Scheme.Hom.AbsoluteProjModel)
    (a : D.ring) : CommRingCat.{u} := by
  -- Local instance justification (defeq pin): expose the stored homogeneous carriers.
  letI : SetLike D.grade D.ring := D.gradeSetLike
  -- Local instance justification (defeq pin): expose the stored additive subgroup structures.
  letI : AddSubgroupClass D.grade D.ring := D.gradeAddSubgroupClass
  -- Local instance justification (defeq pin): expose the stored graded-ring structure.
  letI : GradedRing D.grading := D.grading_inst
  exact CommRingCat.of (HomogeneousLocalization.Away D.grading a)

/-- The canonical spectrum coordinate of a positive-degree basic open in an explicit affine
relative-Proj model. -/
noncomputable def relativeProjBasicOpenIsoSpec (D : Scheme.Hom.AbsoluteProjModel)
    (a : D.ring)
    (ha : a ∈ @SetLike.coe D.grade D.ring D.gradeSetLike (D.grading 1)) :
    (relativeProjBasicOpen D a).toScheme ≅ Spec (relativeProjAwayRing D a) := by
  -- Local instance justification (defeq pin): expose the stored homogeneous carriers.
  letI : SetLike D.grade D.ring := D.gradeSetLike
  -- Local instance justification (defeq pin): expose the stored additive subgroup structures.
  letI : AddSubgroupClass D.grade D.ring := D.gradeAddSubgroupClass
  -- Local instance justification (defeq pin): expose the stored graded-ring structure.
  letI : GradedRing D.grading := D.grading_inst
  exact AlgebraicGeometry.Proj.basicOpenIsoSpec D.grading a ha (by omega)

/-- The ring of ambient functions pulled back to an open in the source of a projective-bundle
section. -/
abbrev ambientSectionRing {T : Scheme.{u}} {f : T ⟶ X} (σ : Lift π f) (U : T.Opens) :=
  ((TopCat.Sheaf.pullback CommRingCat.{u} σ.baseChangeSection.toShHom.hom.base).obj
    (pullback π f).sheaf).obj.obj (op U)

/-- The inverse-image structure-sheaf map of a projective-bundle section. -/
abbrev sectionStructureMap {T : Scheme.{u}} {f : T ⟶ X} (σ : Lift π f) :=
  RingedSpace.Hom.inverseImageStructureSheafHomComm σ.baseChangeSection.toShHom

/-- A standard-open factorization of a split quotient over an arbitrary affine refinement of
the test scheme.  The ambient open is identified with a genuine degree-one basic open in an
affine model of the supplied symmetric relative-Proj presentation, and its coordinate algebra
is identified over the ring of functions on the source open. -/
structure StandardOpenFactorization (S : SymmetricPresentation π ℰ)
    {T : Scheme.{u}} (f : T ⟶ X) (σ : Lift π f) (U : T.Opens)
    (C : AlgebraicGeometry.Proj.SymmetricQuotientChart
      (T.presheaf.obj (op U)) (((Scheme.Modules.pullback f).obj ℰ).val.obj (op U))) where
  /-- A point selecting one of the affine relative-Proj models in the symmetric presentation. -/
  relativeProjPoint : X
  /-- The degree-one homogeneous element defining the standard open in that affine model. -/
  degreeOneDenominator :
    (S.relativeProj.affineChart relativeProjPoint).affineAlgebra.ring
  /-- The denominator is homogeneous of degree one. -/
  degreeOneDenominator_mem :
    degreeOneDenominator ∈
      @SetLike.coe
        (S.relativeProj.affineChart relativeProjPoint).affineAlgebra.grade
        (S.relativeProj.affineChart relativeProjPoint).affineAlgebra.ring
        (S.relativeProj.affineChart relativeProjPoint).affineAlgebra.gradeSetLike
        ((S.relativeProj.affineChart relativeProjPoint).affineAlgebra.grading 1)
  /-- The affine ambient open through which the restricted section factors. -/
  ambientOpen : (pullback π f).Opens
  /-- The ambient open is the actual basic open cut out by the degree-one denominator in the
  chosen affine relative-Proj model. -/
  ambientBasicOpenIso : ambientOpen.toScheme ≅
    (relativeProjBasicOpen
      (S.relativeProj.affineChart relativeProjPoint).affineAlgebra
      degreeOneDenominator).toScheme
  /-- The base-section ring acts on the degree-zero homogeneous localization of the affine
  relative-Proj model. -/
  relativeProjBaseMap : T.presheaf.obj (op U) →+*
    relativeProjAwayRing
      (S.relativeProj.affineChart relativeProjPoint).affineAlgebra
      degreeOneDenominator
  /-- The split-quotient coordinate is an algebra equivalence over the base-section ring with
  the actual degree-zero homogeneous localization. -/
  standardOpenAlgebraEquiv :
    -- Local instance justification (noncanonical choice): the explicit coordinate carries a chosen relative-Proj base map that must not become a global algebra instance.
    letI : Algebra (T.presheaf.obj (op U))
        (relativeProjAwayRing
          (S.relativeProj.affineChart relativeProjPoint).affineAlgebra
          degreeOneDenominator) := relativeProjBaseMap.toAlgebra
    SymmetricAlgebra (T.presheaf.obj (op U)) (LinearMap.ker C.quotient) ≃ₐ[
      T.presheaf.obj (op U)]
        relativeProjAwayRing
          (S.relativeProj.affineChart relativeProjPoint).affineAlgebra
          degreeOneDenominator
  /-- An affine coordinate on the source open. -/
  baseCoordinate :
    Spec (CommRingCat.of (T.presheaf.obj (op U))) ≅ U.toScheme
  /-- The base-section ring acts on the actual ambient section ring. -/
  ambientBaseMap : T.presheaf.obj (op U) →+* ambientSectionRing σ U
  /-- The actual ambient section ring is identified with the symmetric algebra of the quotient
  kernel as an algebra over the base-section ring. -/
  ambientSectionsEquiv :
    -- Local instance justification (noncanonical choice): the explicit ambient coordinate carries a chosen base map that must not become a global algebra instance.
    letI : Algebra (T.presheaf.obj (op U)) (ambientSectionRing σ U) :=
      ambientBaseMap.toAlgebra
    SymmetricAlgebra (T.presheaf.obj (op U)) (LinearMap.ker C.quotient) ≃ₐ[
      T.presheaf.obj (op U)] ambientSectionRing σ U
  /-- The ambient coordinate intertwines the inverse-image structure map with symmetric-algebra
  augmentation. -/
  ambientSections_comm : ∀ x,
    ((sectionStructureMap σ).hom.app (op U)).hom (ambientSectionsEquiv x) =
      SymmetricAlgebra.algebraMapInv x
  /-- The section restricted to the chosen source and ambient opens. -/
  restrictedSection : U.toScheme ⟶ ambientOpen.toScheme
  /-- The restricted section is compatible with the two open immersions. -/
  restrictedSection_comm :
    restrictedSection ≫ ambientOpen.ι = U.ι ≫ σ.baseChangeSection
  /-- In the chosen affine coordinates, the restricted section is the augmentation morphism. -/
  coordinateSquare :
    -- Local instance justification (noncanonical choice): the coordinate square uses the factorization's explicitly stored relative-Proj base map.
    letI : Algebra (T.presheaf.obj (op U))
        (relativeProjAwayRing
          (S.relativeProj.affineChart relativeProjPoint).affineAlgebra
          degreeOneDenominator) := relativeProjBaseMap.toAlgebra
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (SymmetricAlgebra.augmentationIdeal (T.presheaf.obj (op U))
          (LinearMap.ker C.quotient)))) ≫
        ((Scheme.Spec.mapIso
            standardOpenAlgebraEquiv.toRingEquiv.toCommRingCatIso.op).symm ≪≫
          (relativeProjBasicOpenIsoSpec
            (S.relativeProj.affineChart relativeProjPoint).affineAlgebra
            degreeOneDenominator degreeOneDenominator_mem).symm ≪≫
          ambientBasicOpenIso.symm).hom =
      ((Scheme.Spec.mapIso
          (SymmetricAlgebra.augmentationQuotientEquiv
            (T.presheaf.obj (op U))
            (LinearMap.ker C.quotient)).toCommRingCatIso.op).symm ≪≫
        baseCoordinate).hom ≫ restrictedSection

namespace StandardOpenFactorization

variable {S : SymmetricPresentation π ℰ} {T : Scheme.{u}} {f : T ⟶ X}
variable {σ : Lift π f} {U : T.Opens}
variable {C : AlgebraicGeometry.Proj.SymmetricQuotientChart
  (T.presheaf.obj (op U)) (((Scheme.Modules.pullback f).obj ℰ).val.obj (op U))}

/-- Construct a standard-open factorization from affine source and ambient coordinates whose
restricted section is the symmetric-algebra augmentation. -/
def ofCoordinates (S : SymmetricPresentation π ℰ) {T : Scheme.{u}}
    (f : T ⟶ X) (σ : Lift π f) (U : T.Opens)
    (C : AlgebraicGeometry.Proj.SymmetricQuotientChart
      (T.presheaf.obj (op U)) (((Scheme.Modules.pullback f).obj ℰ).val.obj (op U)))
    (relativeProjPoint : X)
    (degreeOneDenominator :
      (S.relativeProj.affineChart relativeProjPoint).affineAlgebra.ring)
    (degreeOneDenominator_mem :
      degreeOneDenominator ∈
        @SetLike.coe
          (S.relativeProj.affineChart relativeProjPoint).affineAlgebra.grade
          (S.relativeProj.affineChart relativeProjPoint).affineAlgebra.ring
          (S.relativeProj.affineChart relativeProjPoint).affineAlgebra.gradeSetLike
          ((S.relativeProj.affineChart relativeProjPoint).affineAlgebra.grading 1))
    (ambientOpen : (pullback π f).Opens)
    (ambientBasicOpenIso : ambientOpen.toScheme ≅
      (relativeProjBasicOpen
        (S.relativeProj.affineChart relativeProjPoint).affineAlgebra
        degreeOneDenominator).toScheme)
    (relativeProjBaseMap : T.presheaf.obj (op U) →+*
      relativeProjAwayRing
        (S.relativeProj.affineChart relativeProjPoint).affineAlgebra
        degreeOneDenominator)
    (standardOpenAlgebraEquiv :
      -- Local instance justification (noncanonical choice): the supplied algebra equivalence uses its explicit relative-Proj base map only in this parameter type.
      letI : Algebra (T.presheaf.obj (op U))
          (relativeProjAwayRing
            (S.relativeProj.affineChart relativeProjPoint).affineAlgebra
            degreeOneDenominator) := relativeProjBaseMap.toAlgebra
      SymmetricAlgebra (T.presheaf.obj (op U)) (LinearMap.ker C.quotient) ≃ₐ[
        T.presheaf.obj (op U)]
          relativeProjAwayRing
            (S.relativeProj.affineChart relativeProjPoint).affineAlgebra
            degreeOneDenominator)
    (baseCoordinate : Spec (CommRingCat.of (T.presheaf.obj (op U))) ≅ U.toScheme)
    (ambientBaseMap : T.presheaf.obj (op U) →+* ambientSectionRing σ U)
    (ambientSectionsEquiv :
      -- Local instance justification (noncanonical choice): the supplied ambient equivalence uses its explicit base map only in this parameter type.
      letI : Algebra (T.presheaf.obj (op U)) (ambientSectionRing σ U) :=
        ambientBaseMap.toAlgebra
      SymmetricAlgebra (T.presheaf.obj (op U)) (LinearMap.ker C.quotient) ≃ₐ[
        T.presheaf.obj (op U)] ambientSectionRing σ U)
    (ambientSections_comm : ∀ x,
      ((sectionStructureMap σ).hom.app (op U)).hom (ambientSectionsEquiv x) =
        SymmetricAlgebra.algebraMapInv x)
    (restrictedSection : U.toScheme ⟶ ambientOpen.toScheme)
    (restrictedSection_comm :
      restrictedSection ≫ ambientOpen.ι = U.ι ≫ σ.baseChangeSection)
    (coordinateSquare :
      -- Local instance justification (noncanonical choice): the supplied coordinate square uses its explicit relative-Proj base map only in this parameter type.
      letI : Algebra (T.presheaf.obj (op U))
          (relativeProjAwayRing
            (S.relativeProj.affineChart relativeProjPoint).affineAlgebra
            degreeOneDenominator) := relativeProjBaseMap.toAlgebra
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (SymmetricAlgebra.augmentationIdeal (T.presheaf.obj (op U))
            (LinearMap.ker C.quotient)))) ≫
          ((Scheme.Spec.mapIso
              standardOpenAlgebraEquiv.toRingEquiv.toCommRingCatIso.op).symm ≪≫
            (relativeProjBasicOpenIsoSpec
              (S.relativeProj.affineChart relativeProjPoint).affineAlgebra
              degreeOneDenominator degreeOneDenominator_mem).symm ≪≫
            ambientBasicOpenIso.symm).hom =
        ((Scheme.Spec.mapIso
            (SymmetricAlgebra.augmentationQuotientEquiv
              (T.presheaf.obj (op U))
              (LinearMap.ker C.quotient)).toCommRingCatIso.op).symm ≪≫
          baseCoordinate).hom ≫ restrictedSection) :
    StandardOpenFactorization S f σ U C :=
  { relativeProjPoint
    degreeOneDenominator
    degreeOneDenominator_mem
    ambientOpen
    ambientBasicOpenIso
    relativeProjBaseMap
    standardOpenAlgebraEquiv
    baseCoordinate
    ambientBaseMap
    ambientSectionsEquiv
    ambientSections_comm
    restrictedSection
    restrictedSection_comm
    coordinateSquare }

/-- The actual relative-Proj basic open underlying a standard-open factorization. -/
def relativeProjOpen (F : StandardOpenFactorization S f σ U C) :
    (S.relativeProj.affineChart F.relativeProjPoint).affineAlgebra.proj.Opens :=
  relativeProjBasicOpen
    (S.relativeProj.affineChart F.relativeProjPoint).affineAlgebra
    F.degreeOneDenominator

/-- The canonical spectrum coordinate on the relative-Proj basic open of a standard-open
factorization. -/
noncomputable def relativeProjOpenIsoSpec (F : StandardOpenFactorization S f σ U C) :
    F.relativeProjOpen.toScheme ≅
      Spec (relativeProjAwayRing
        (S.relativeProj.affineChart F.relativeProjPoint).affineAlgebra
        F.degreeOneDenominator) :=
  relativeProjBasicOpenIsoSpec
    (S.relativeProj.affineChart F.relativeProjPoint).affineAlgebra
    F.degreeOneDenominator F.degreeOneDenominator_mem

/-- The symmetric-algebra coordinate on the ambient open, derived from the actual
relative-Proj basic-open coordinate. -/
noncomputable def targetCoordinate (F : StandardOpenFactorization S f σ U C) :
    Spec (CommRingCat.of
      (SymmetricAlgebra (T.presheaf.obj (op U)) (LinearMap.ker C.quotient))) ≅
      F.ambientOpen.toScheme := by
  -- Local instance justification (noncanonical choice): deriving the target coordinate temporarily interprets the factorization's explicit relative-Proj base map.
  letI : Algebra (T.presheaf.obj (op U))
      (relativeProjAwayRing
        (S.relativeProj.affineChart F.relativeProjPoint).affineAlgebra
        F.degreeOneDenominator) := F.relativeProjBaseMap.toAlgebra
  exact
    (Scheme.Spec.mapIso F.standardOpenAlgebraEquiv.toRingEquiv.toCommRingCatIso.op).symm ≪≫
      F.relativeProjOpenIsoSpec.symm ≪≫ F.ambientBasicOpenIso.symm

/-- The affine source coordinate obtained from the augmentation quotient and the chosen affine
coordinate on the source open. -/
noncomputable def sourceCoordinate (F : StandardOpenFactorization S f σ U C) :
    Spec (CommRingCat.of
      (SymmetricAlgebra (T.presheaf.obj (op U)) (LinearMap.ker C.quotient) ⧸
        SymmetricAlgebra.augmentationIdeal (T.presheaf.obj (op U))
          (LinearMap.ker C.quotient))) ≅ U.toScheme :=
  (Scheme.Spec.mapIso
    (SymmetricAlgebra.augmentationQuotientEquiv
      (T.presheaf.obj (op U)) (LinearMap.ker C.quotient)).toCommRingCatIso.op).symm ≪≫
    F.baseCoordinate

/-- The closed immersion defined by symmetric-algebra augmentation. -/
def augmentationMorphism (_ : StandardOpenFactorization S f σ U C) :
    Spec (CommRingCat.of
      (SymmetricAlgebra (T.presheaf.obj (op U)) (LinearMap.ker C.quotient) ⧸
        SymmetricAlgebra.augmentationIdeal (T.presheaf.obj (op U))
          (LinearMap.ker C.quotient))) ⟶
      Spec (CommRingCat.of
        (SymmetricAlgebra (T.presheaf.obj (op U)) (LinearMap.ker C.quotient))) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
    (SymmetricAlgebra.augmentationIdeal (T.presheaf.obj (op U))
      (LinearMap.ker C.quotient))))

/-- The source coordinate is the spectrum of the canonical augmentation quotient equivalence. -/
theorem sourceCoordinate_eq_augmentation (F : StandardOpenFactorization S f σ U C) :
    F.sourceCoordinate =
      (Scheme.Spec.mapIso
        (SymmetricAlgebra.augmentationQuotientEquiv
          (T.presheaf.obj (op U)) (LinearMap.ker C.quotient)).toCommRingCatIso.op).symm ≪≫
        F.baseCoordinate := sorry

/-- In the chosen source and target coordinates, the restricted section is the augmentation
closed immersion. -/
theorem sectionAugmentation_comm (F : StandardOpenFactorization S f σ U C) :
    F.augmentationMorphism ≫ F.targetCoordinate.hom =
      F.sourceCoordinate.hom ≫ F.restrictedSection := sorry

/-- The restricted-section square in the standard-open coordinates is cartesian. -/
theorem restrictedSection_pullback (F : StandardOpenFactorization S f σ U C) :
    IsPullback F.sourceCoordinate.hom F.augmentationMorphism
      F.restrictedSection F.targetCoordinate.hom := sorry

/-- The augmentation ideal maps to the sectionwise conormal ideal through the actual ambient
coordinate ring isomorphism. -/
def coordinateIdealMap (F : StandardOpenFactorization S f σ U C) :
    SymmetricAlgebra.augmentationIdeal (T.presheaf.obj (op U))
        (LinearMap.ker C.quotient) →+
      conormalIdeal (sectionStructureMap σ) (op U) where
  toFun x :=
    ⟨F.ambientSectionsEquiv x.1, by
      change ((sectionStructureMap σ).hom.app (op U)).hom
          (F.ambientSectionsEquiv x.1) = 0
      rw [F.ambientSections_comm]
      exact x.2⟩
  map_zero' := by
    apply Subtype.ext
    exact F.ambientSectionsEquiv.map_zero
  map_add' x y := by
    apply Subtype.ext
    exact F.ambientSectionsEquiv.map_add x.1 y.1

/-- The additive generator map from the augmentation ideal to local conormal sections. -/
noncomputable def conormalGenerator (F : StandardOpenFactorization S f σ U C) :
    SymmetricAlgebra.augmentationIdeal (T.presheaf.obj (op U))
        (LinearMap.ker C.quotient) →+
      (Scheme.Hom.conormalSheaf σ.baseChangeSection).val.obj (op U) :=
  ((conormalSourcePresheafUnit (sectionStructureMap σ)).app (op U)).hom.toAddMonoidHom.comp
    ((conormalIdeal (sectionStructureMap σ) (op U)).toCotangent.toAddMonoidHom.comp
      F.coordinateIdealMap)

set_option maxHeartbeats 1000000 in
/-- The additive augmentation-cotangent map underlying the standard-open conormal comparison. -/
noncomputable def conormalTransportAdd (F : StandardOpenFactorization S f σ U C) :
    (SymmetricAlgebra.augmentationIdeal (T.presheaf.obj (op U))
      (LinearMap.ker C.quotient)).Cotangent →+
      (Scheme.Hom.conormalSheaf σ.baseChangeSection).val.obj (op U) :=
  (Ideal.Cotangent.lift
    { toFun := F.conormalGenerator
      map_add' := F.conormalGenerator.map_add
      map_smul' := fun n x => F.conormalGenerator.map_zsmul n x }
    (fun x y => by
      change F.conormalGenerator (x * y) = 0
      change ((conormalSourcePresheafUnit (sectionStructureMap σ)).app
          (op U)).hom ((conormalIdeal (sectionStructureMap σ) (op U)).toCotangent
            (F.coordinateIdealMap (x * y))) = 0
      rw [← map_zero ((conormalSourcePresheafUnit (sectionStructureMap σ)).app
        (op U)).hom]
      apply congrArg ((conormalSourcePresheafUnit (sectionStructureMap σ)).app
        (op U)).hom
      apply ((conormalIdeal (sectionStructureMap σ) (op U)).toCotangent_eq_zero _).2
      change F.ambientSectionsEquiv (x.1 * y.1) ∈
        conormalIdeal (sectionStructureMap σ) (op U) ^ 2
      rw [pow_two, map_mul]
      exact Ideal.mul_mem_mul
        (F.coordinateIdealMap x).2 (F.coordinateIdealMap y).2)).toAddMonoidHom

/-- The additive standard-open conormal comparison is linear over the source-open section ring. -/
theorem conormalTransport_naturality (F : StandardOpenFactorization S f σ U C)
    (r : T.presheaf.obj (op U))
    (x : (SymmetricAlgebra.augmentationIdeal (T.presheaf.obj (op U))
      (LinearMap.ker C.quotient)).Cotangent) :
    F.conormalTransportAdd (r • x) = r • F.conormalTransportAdd x := sorry

/-- The conormal comparison derived from the augmentation coordinate of a standard-open
factorization. -/
noncomputable def conormalTransport (F : StandardOpenFactorization S f σ U C) :
    ModuleCat.of (T.presheaf.obj (op U))
        (SymmetricAlgebra.augmentationIdeal (T.presheaf.obj (op U))
          (LinearMap.ker C.quotient)).Cotangent ⟶
      (Scheme.Hom.conormalSheaf σ.baseChangeSection).val.obj (op U) :=
  ModuleCat.ofHom
    { toFun := F.conormalTransportAdd
      map_add' := F.conormalTransportAdd.map_add
      map_smul' := F.conormalTransport_naturality }

/-- The standard-open conormal comparison is an isomorphism. -/
theorem conormalTransport_isIso (F : StandardOpenFactorization S f σ U C) :
    IsIso F.conormalTransport := sorry

/-- A standard-open factorization uses a degree-one basic open in the supplied relative-Proj
presentation, algebra coordinates over the base-section ring, and the restricted augmentation
square. -/
theorem spec (F : StandardOpenFactorization S f σ U C) :
    -- Local instance justification (noncanonical choice): these algebra-coordinate laws temporarily interpret the factorization's explicit relative-Proj base map.
    letI : Algebra (T.presheaf.obj (op U))
        (relativeProjAwayRing
          (S.relativeProj.affineChart F.relativeProjPoint).affineAlgebra
          F.degreeOneDenominator) := F.relativeProjBaseMap.toAlgebra
    -- Local instance justification (noncanonical choice): these algebra-coordinate laws temporarily interpret the factorization's explicit ambient base map.
    letI : Algebra (T.presheaf.obj (op U)) (ambientSectionRing σ U) :=
      F.ambientBaseMap.toAlgebra
    F.degreeOneDenominator ∈
        @SetLike.coe
          (S.relativeProj.affineChart F.relativeProjPoint).affineAlgebra.grade
          (S.relativeProj.affineChart F.relativeProjPoint).affineAlgebra.ring
          (S.relativeProj.affineChart F.relativeProjPoint).affineAlgebra.gradeSetLike
          ((S.relativeProj.affineChart F.relativeProjPoint).affineAlgebra.grading 1) ∧
      F.targetCoordinate =
        (Scheme.Spec.mapIso
            F.standardOpenAlgebraEquiv.toRingEquiv.toCommRingCatIso.op).symm ≪≫
          F.relativeProjOpenIsoSpec.symm ≪≫ F.ambientBasicOpenIso.symm ∧
      (∀ r : T.presheaf.obj (op U),
        F.standardOpenAlgebraEquiv
            (algebraMap (T.presheaf.obj (op U))
              (SymmetricAlgebra (T.presheaf.obj (op U))
                (LinearMap.ker C.quotient)) r) =
          F.relativeProjBaseMap r) ∧
      (∀ r : T.presheaf.obj (op U),
        F.ambientSectionsEquiv
            (algebraMap (T.presheaf.obj (op U))
              (SymmetricAlgebra (T.presheaf.obj (op U))
                (LinearMap.ker C.quotient)) r) =
          F.ambientBaseMap r) ∧
      F.augmentationMorphism ≫ F.targetCoordinate.hom =
        F.sourceCoordinate.hom ≫ F.restrictedSection ∧
      (∀ x,
        ((sectionStructureMap σ).hom.app (op U)).hom (F.ambientSectionsEquiv x) =
          SymmetricAlgebra.algebraMapInv x) ∧
      F.restrictedSection ≫ F.ambientOpen.ι = U.ι ≫ σ.baseChangeSection := sorry

end StandardOpenFactorization

end AlgebraicGeometry.Scheme.ProjectiveBundle.SymmetricPresentation
