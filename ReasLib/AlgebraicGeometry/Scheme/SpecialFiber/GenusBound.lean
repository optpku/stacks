/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.SpecialFiber
public import ReasLib.AlgebraicGeometry.NumericalType.TopologicalGenus
public import ReasLib.AlgebraicGeometry.Scheme.Model.SpecialFiberDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GeometricGenus

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- If the special fibre of a regular proper flat curve model has a smooth rational point,
the first structure-sheaf cohomology dimension of its reduction bounds the sum of the
topological genus of its numerical type and its geometric genus. -/
theorem genusSum_le_reductionH1
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (s : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶
      f.fiber (IsLocalRing.closedPoint R))
    (h_section : s ≫ f.fiberToSpecResidueField (IsLocalRing.closedPoint R) = 𝟙 _)
    (h_smooth : (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)).SmoothAt
      (s (IsLocalRing.closedPoint
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))))) :
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
          Scheme.Modules (Scheme.reduction (f.fiber (IsLocalRing.closedPoint R)))) 1 := sorry

end AlgebraicGeometry.Scheme.Hom
