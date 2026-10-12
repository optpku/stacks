/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap53.Lemma_53_18_2
public import stacks_project.Chap55.Definition_55_3_11_TopologicalGenus
public import stacks_project.Chap55.Lemma_55_11_3
public import ReasLib.AlgebraicGeometry.Scheme.Model.SpecialFiberDimension
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.GenusBound

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Hom CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

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

section ModelDimension

include hCommRing hDomain hDVR hField hAlgebra hFractionRing hπ hCurve hSmooth
  hProjective h_globalSections hFlat hFiniteType hProper hRegular genericFiberIso

/-- The special fibre of the regular proper curve model has dimension at most one. -/
theorem modelFiber_dimension_le_one :
    topologicalKrullDim (f.fiber (IsLocalRing.closedPoint R)) ≤ 1 :=
  regularModel_specialFiber_dimension_le_one R K π hπ C h_globalSections f genericFiberIso

variable (n : ℕ)
variable (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))

/-- Each reduced component of the special fibre has dimension at most one. -/
theorem modelComponent_dimension_le_one (i : Fin n) :
    topologicalKrullDim (situationComponent R f n components i) ≤ 1 :=
  SpecialFiber.component_dimension_le_one C h_globalSections f genericFiberIso n components i

end ModelDimension

/-- Each component of the special fibre is proper over the residue field. -/
theorem situationComponentIsProper (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (i : Fin n) :
    IsProper (situationComponentToResidueField R f n components i) :=
  SpecialFiber.instIsProperComponentToResidueField f (components i)

/- Lemma 55.11.9: in Situation 55.9.3, a smooth rational point on the special
fibre implies that the degree-one structure-sheaf cohomology dimension of its
reduction bounds the sum of its topological and geometric genera. -/
@[stacks 0CEA] #check (AlgebraicGeometry.Scheme.Hom.genusSum_le_reductionH1 :
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (s : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶
      f.fiber (IsLocalRing.closedPoint R))
    (h_section : s ≫ f.fiberToSpecResidueField (IsLocalRing.closedPoint R) = 𝟙 _)
    (h_smooth : (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)).SmoothAt
      (s (IsLocalRing.closedPoint
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))))),
    NumericalType.topologicalGenus
        (NumericalType.ofSpecialFiber R K π hπ C h_globalSections f genericFiberIso n
          components (fun i ↦ SpecialFiber.instIsProperComponentToResidueField f (components i))
          (fun i ↦ SpecialFiber.component_dimension_le_one
            C h_globalSections f genericFiberIso n components i)) +
      @GeometricGenus.ofScheme _ _
        (Over.mk (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)) :
          SchemeOverField ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)))
        (fiberToSpecResidueField_isProper f (IsLocalRing.closedPoint R))
        (regularModel_specialFiber_dimension_le_one R K π hπ C h_globalSections f
          genericFiberIso) ≤
      cohomologyFinrank (Scheme.reductionι (f.fiber (IsLocalRing.closedPoint R)) ≫
        f.fiberToSpecResidueField (IsLocalRing.closedPoint R))
        (SheafOfModules.unit (Scheme.reduction (f.fiber (IsLocalRing.closedPoint R))).ringCatSheaf :
          Scheme.Modules (Scheme.reduction (f.fiber (IsLocalRing.closedPoint R)))) 1)
