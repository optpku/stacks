module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.GenusEquality

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.SpecialFiber

section

variable (R K : Type u) [hCommRing : CommRing R] [hDomain : IsDomain R]
  [hDVR : IsDiscreteValuationRing R]
variable [hField : Field K] [hAlgebra : Algebra R K] [hFractionRing : IsFractionRing R K]
variable (π : R) (hπ : Irreducible π)
variable (C : SchemeOverField K) [hCurve : Curve C] [hSmooth : Smooth C.hom]
  [hProjective : Projective C.hom]
variable (h_globalSections : Function.Bijective (globalSectionsMap C.hom))
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable [hFlat : Flat f] [hFiniteType : Scheme.Hom.FiniteType f]
  [hProper : IsProper f] [hRegular : Scheme.Regular X]
variable (genericFiberIso : C ≅ Over.mk
  (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
variable (n : ℕ)
variable (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
variable (s : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶
  f.fiber (IsLocalRing.closedPoint R))
variable (h_section : s ≫ f.fiberToSpecResidueField (IsLocalRing.closedPoint R) = 𝟙 _)
variable (h_smooth : (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)).SmoothAt
  (s (IsLocalRing.closedPoint
    ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)))))
variable (h_eq :
    NumericalType.topologicalGenus
        (NumericalType.ofSpecialFiber R K π hπ C h_globalSections f genericFiberIso n
          components (fun i ↦ instIsProperComponentToResidueField f (components i))
          (fun i ↦ component_dimension_le_one C h_globalSections f genericFiberIso n
            components i)) +
      @GeometricGenus.ofScheme _ _
        (Over.mk (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)) :
          SchemeOverField ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)))
        (fiberToSpecResidueField_isProper f (IsLocalRing.closedPoint R))
        (regularModel_specialFiber_dimension_le_one R K π hπ C h_globalSections f
          genericFiberIso) =
      cohomologyFinrank (Scheme.reductionι (f.fiber (IsLocalRing.closedPoint R)) ≫
        f.fiberToSpecResidueField (IsLocalRing.closedPoint R))
        (SheafOfModules.unit (Scheme.reduction (f.fiber (IsLocalRing.closedPoint R))).ringCatSheaf :
          Scheme.Modules (Scheme.reduction (f.fiber (IsLocalRing.closedPoint R)))) 1)

/- Lemma 55.11.10 -/
@[stacks 0CEE] #check
  (AlgebraicGeometry.Scheme.Hom.SpecialFiber.uniqueComponentContainingPoint
    R K π hπ C h_globalSections f genericFiberIso n components s h_section h_smooth h_eq :
    ∃! i : Fin n,
      s (IsLocalRing.closedPoint
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
          (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i))

/- Lemma 55.11.10 (2) -/
@[stacks 0CEE] #check
  (AlgebraicGeometry.Scheme.Hom.SpecialFiber.componentContainingPointIsCurve
    R K π hπ C h_globalSections f genericFiberIso n components s h_section h_smooth h_eq
    : ∀ (i : Fin n),
      s (IsLocalRing.closedPoint
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i) →
      Curve (Over.mk (componentToResidueField f (components i))))

/- Lemma 55.11.10 (3) -/
@[stacks 0CEE] #check
  (AlgebraicGeometry.Scheme.Hom.SpecialFiber.componentContainingPointIsSmooth
    R K π hπ C h_globalSections f genericFiberIso n components s h_section h_smooth h_eq
    : ∀ (i : Fin n),
      s (IsLocalRing.closedPoint
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i) →
      Smooth (componentToResidueField f (components i)))

/- Lemma 55.11.10 (4) -/
@[stacks 0CEE] #check
  (AlgebraicGeometry.Scheme.Hom.SpecialFiber.componentContainingPointIsProjective
    R K π hπ C h_globalSections f genericFiberIso n components s h_section h_smooth h_eq
    : ∀ (i : Fin n),
      s (IsLocalRing.closedPoint
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i) →
      Projective (componentToResidueField f (components i)))

/- Lemma 55.11.10 (5) -/
@[stacks 0CEE] #check
  (AlgebraicGeometry.Scheme.Hom.SpecialFiber.componentContainingPointIsGeometricallyIrreducible
    R K π hπ C h_globalSections f genericFiberIso n components s h_section h_smooth h_eq
    : ∀ (i : Fin n),
      s (IsLocalRing.closedPoint
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i) →
      GeometricallyIrreducible (componentToResidueField f (components i)))

section

variable (j : Fin n)

-- Supply properness explicitly: instance search cannot recover the model from the
-- composite morphism of the component to the residue field.

/- Lemma 55.11.10 (6) -/
@[stacks 0CEE] #check
  (@AlgebraicGeometry.globalSectionsFiniteDimensional _ _ _
    (componentToResidueField f (components j))
    (instIsProperComponentToResidueField f (components j)) :
    FiniteDimensional
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
        (globalSectionsAlg (componentToResidueField f (components j))))

end

/- Lemma 55.11.10 (7) -/
@[stacks 0CEE] #check
  (AlgebraicGeometry.Scheme.Hom.SpecialFiber.otherComponentSectionsSeparable
    R K π hπ C h_globalSections f genericFiberIso n components s h_section h_smooth h_eq
    : ∀ (i j : Fin n),
      s (IsLocalRing.closedPoint
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i) →
      j ≠ i →
      Algebra.IsSeparable
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
        (globalSectionsAlg (componentToResidueField f (components j))))

/- Lemma 55.11.10 (8) -/
@[stacks 0CEE] #check
  (AlgebraicGeometry.Scheme.Hom.SpecialFiber.otherComponentHasRationalPointOverSections
    R K π hπ C h_globalSections f genericFiberIso n components s h_section h_smooth h_eq
    : ∀ (i j : Fin n),
      s (IsLocalRing.closedPoint
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i) →
      j ≠ i →
      SchemeOverField.BaseField.hasRationalPoint
        (Over.mk (component f (components j)).toSpecΓ : SchemeOverField
          (globalSectionsAlg (componentToResidueField f (components j)))))

/- Lemma 55.11.10 (9) -/
@[stacks 0CEE] #check
  (AlgebraicGeometry.Scheme.Hom.SpecialFiber.otherComponentSmoothOverSections
    R K π hπ C h_globalSections f genericFiberIso n components s h_section h_smooth h_eq
    : ∀ (i j : Fin n),
      s (IsLocalRing.closedPoint
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i) →
      j ≠ i →
      Smooth (component f (components j)).toSpecΓ)

end

end AlgebraicGeometry.Scheme.Hom.SpecialFiber
