module

public import ReasLib.AlgebraicGeometry.Scheme.Model.RationalPoint
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SectionComponent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.BaseField
public import stacks_project.Chap53.Definition_53_8_1_Genus
public import stacks_project.Chap55.Lemma_55_9_1_SpecialFiber
public import stacks_project.Chap55.Lemma_55_9_2
public import stacks_project.Chap55.Lemma_55_9_6_Components
public import stacks_project.Chap55.Situation_55_9_3
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable (R K : Type u) [h_commRing : CommRing R] [h_domain : IsDomain R]
variable [h_dvr : IsDiscreteValuationRing R]
variable [h_field : Field K] [h_algebra : Algebra R K]
variable [h_fractionRing : IsFractionRing R K]
variable (π : R) (hπ : Irreducible π)
variable (C : SchemeOverField K) [h_curve : Curve C] [h_smooth : Smooth C.hom]
variable [h_projective : AlgebraicGeometry.Projective C.hom]
variable (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
variable (h_C_point : SchemeOverField.BaseField.hasRationalPoint C)
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable [h_flat : Flat f] [h_finiteType : Scheme.Hom.FiniteType f]
variable [h_proper : IsProper f] [h_regular : Scheme.Regular X]
variable (genericFiberIso : C ≅ Over.mk
  (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
variable (n : ℕ)
variable (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))

/- Lemma 55.11.7 (1): in Situation 55.9.3, a `K`-rational point of `C` extends to a
smooth `k`-rational point of the special fibre. -/
@[stacks 0CE8] #check (AlgebraicGeometry.Scheme.Hom.exists_smoothRationalPoint_specialFiber R K π hπ C
    h_globalSections h_C_point f genericFiberIso n components :
      ∃ s : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶
          f.fiber (IsLocalRing.closedPoint R),
        s ≫ f.fiberToSpecResidueField (IsLocalRing.closedPoint R) = 𝟙 _ ∧
          (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)).SmoothAt
            (s (IsLocalRing.closedPoint
              ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)))))

/- Lemma 55.11.7 (2): a component containing the extended smooth rational point has global
functions equal to the residue field. -/
@[stacks 0CE8] #check (AlgebraicGeometry.Scheme.Hom.component_globalSectionsMap_bijective R K π hπ C
    h_globalSections h_C_point f genericFiberIso n components :
      ∀ (s : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶
          f.fiber (IsLocalRing.closedPoint R))
        (h_section : s ≫ f.fiberToSpecResidueField (IsLocalRing.closedPoint R) = 𝟙 _)
        (h_smooth : (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)).SmoothAt
          (s (IsLocalRing.closedPoint
            ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)))))
        (i : Fin n),
        s (IsLocalRing.closedPoint
          ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
            (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i) →
          Function.Bijective
            (Scheme.Hom.globalSectionsMap
              (situationComponentToResidueField R f n components i)))

/- Lemma 55.11.7 (3): a component containing the extended smooth rational point has
multiplicity one in the special fibre. -/
@[stacks 0CE8] #check (AlgebraicGeometry.Scheme.Hom.componentMultiplicity_eq_one R K π hπ C h_globalSections
    h_C_point f genericFiberIso n components :
      ∀ (s : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶
          f.fiber (IsLocalRing.closedPoint R))
        (h_section : s ≫ f.fiberToSpecResidueField (IsLocalRing.closedPoint R) = 𝟙 _)
        (h_smooth : (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)).SmoothAt
          (s (IsLocalRing.closedPoint
            ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)))))
        (i : Fin n),
        s (IsLocalRing.closedPoint
          ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
            (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i) →
          f.specialFiberMultiplicities (components i) = 1)

/- Lemma 55.11.7 (4): the special fibre has global functions equal to the residue field. -/
@[stacks 0CE8] #check (AlgebraicGeometry.Scheme.Hom.specialFiber_globalSectionsMap_bijective R K π hπ C
    h_globalSections h_C_point f genericFiberIso n components :
      Function.Bijective
        (Scheme.Hom.globalSectionsMap
          (f.fiberToSpecResidueField (IsLocalRing.closedPoint R))))

/- Lemma 55.11.7 (4a): the special fibre of the regular model has relative dimension one. -/
@[stacks 0CE8] #check (AlgebraicGeometry.Scheme.Hom.specialFiber_dimension_eq_one R K π hπ C h_globalSections
    h_C_point f genericFiberIso n components :
      topologicalKrullDim (f.fiber (IsLocalRing.closedPoint R)) = 1)

/- Lemma 55.11.7 (5): the genus of the special fibre equals the genus of the generic curve. -/
@[stacks 0CE8] #check (AlgebraicGeometry.Scheme.Hom.specialFiber_genus_eq R K π hπ C h_globalSections h_C_point f
    genericFiberIso n components :
      @SchemeOverField.genus _ _
          (Over.mk (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)) :
            SchemeOverField
              ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)))
          (fiberToSpecResidueField_isProper f (IsLocalRing.closedPoint R))
          (specialFiber_dimension_eq_one R K π hπ C h_globalSections h_C_point f
            genericFiberIso n components)
          (specialFiber_globalSectionsMap_bijective R K π hπ C h_globalSections h_C_point f
            genericFiberIso n components) =
        SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections)

end AlgebraicGeometry.Scheme.Hom
