/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.BaseField
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

section

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

include h_commRing h_domain h_dvr h_field h_algebra h_fractionRing hπ h_curve h_smooth
  h_projective h_globalSections h_C_point h_flat h_finiteType h_proper h_regular
  genericFiberIso components

/-- A rational point on the generic smooth projective curve gives a smooth rational point on the
special fibre of a regular proper model over a discrete valuation ring. -/
theorem exists_smoothRationalPoint_specialFiber :
    ∃ s : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶
        f.fiber (IsLocalRing.closedPoint R),
      s ≫ f.fiberToSpecResidueField (IsLocalRing.closedPoint R) = 𝟙 _ ∧
        (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)).SmoothAt
          (s (IsLocalRing.closedPoint
            ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)))) := sorry

/-- A smooth rational point on a special-fibre component makes its global-sections map bijective
onto the residue field. -/
theorem component_globalSectionsMap_bijective
    (s : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶
      f.fiber (IsLocalRing.closedPoint R))
    (h_section : s ≫ f.fiberToSpecResidueField (IsLocalRing.closedPoint R) = 𝟙 _)
    (h_smooth : (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)).SmoothAt
      (s (IsLocalRing.closedPoint
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)))))
    (i : Fin n)
    (h_mem : s (IsLocalRing.closedPoint
      ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i)) :
    Function.Bijective
      (Scheme.Hom.globalSectionsMap
        ((f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentSubschemeι (components i) ≫
          f.fiberToSpecResidueField (IsLocalRing.closedPoint R))) := sorry

/-- A smooth rational point on a special-fibre component forces that component to have
multiplicity one. -/
theorem componentMultiplicity_eq_one
    (s : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶
      f.fiber (IsLocalRing.closedPoint R))
    (h_section : s ≫ f.fiberToSpecResidueField (IsLocalRing.closedPoint R) = 𝟙 _)
    (h_smooth : (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)).SmoothAt
      (s (IsLocalRing.closedPoint
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)))))
    (i : Fin n)
    (h_mem : s (IsLocalRing.closedPoint
      ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i)) :
    f.specialFiberMultiplicities (components i) = 1 := sorry

/-- The special fibre of a regular proper model has the residue field as its global functions. -/
theorem specialFiber_globalSectionsMap_bijective :
    Function.Bijective
      (Scheme.Hom.globalSectionsMap
        (f.fiberToSpecResidueField (IsLocalRing.closedPoint R))) := sorry

/-- The special fibre of a regular model of a smooth curve has dimension one. -/
theorem specialFiber_dimension_eq_one :
    topologicalKrullDim (f.fiber (IsLocalRing.closedPoint R)) = 1 := sorry

/-- The genus of the special fibre of a regular proper model equals the genus of its generic
smooth projective curve. -/
theorem specialFiber_genus_eq :
    @SchemeOverField.genus _ _
        (Over.mk (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)) :
          SchemeOverField ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)))
        (fiberToSpecResidueField_isProper f (IsLocalRing.closedPoint R))
        (specialFiber_dimension_eq_one R K π hπ C h_globalSections h_C_point f
          genericFiberIso n components)
        (specialFiber_globalSectionsMap_bijective R K π hπ C h_globalSections h_C_point f
          genericFiberIso n components) =
      SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections := sorry

end

end AlgebraicGeometry.Scheme.Hom
