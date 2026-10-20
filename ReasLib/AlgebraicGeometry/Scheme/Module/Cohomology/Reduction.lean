/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.MinimalModel
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Sections
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.PrimitiveDivisor
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The canonical degree-`q` cohomology morphism from a scheme to its reduced scheme,
represented on the original scheme by the pushforward of the reduced structure module. -/
noncomputable def reductionCohomologyMap
    {k : Type u} [CommRing k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) (q : ℕ) :
    cohomology p (𝟙_ Y.Modules) q ⟶
      cohomology p ((Scheme.Modules.pushforward (Scheme.reductionι Y)).obj
        (𝟙_ (Scheme.reduction Y).Modules)) q :=
  (cohomologyFunctor p q).map
    ((Scheme.Modules.pullbackPushforwardAdjunction (Scheme.reductionι Y)).unit.app
        (𝟙_ Y.Modules) ≫
      (Scheme.Modules.pushforward (Scheme.reductionι Y)).map
        (Scheme.Modules.pullbackUnitIso (Scheme.reductionι Y)).hom)

/-- The defining cohomology-functor expression for `reductionCohomologyMap`. -/
theorem reductionCohomologyMap_def
    {k : Type u} [CommRing k] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (CommRingCat.of k)) (q : ℕ) :
    reductionCohomologyMap p q =
      (cohomologyFunctor p q).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Scheme.reductionι Y)).unit.app
            (𝟙_ Y.Modules) ≫
          (Scheme.Modules.pushforward (Scheme.reductionι Y)).map
            (Scheme.Modules.pullbackUnitIso (Scheme.reductionι Y)).hom) := sorry

/-- For a minimal model of a smooth projective curve over the fraction field of a discrete
valuation ring, with multiplicity gcd one and constant global functions on the reduced special
fibre, the degree-one structure-sheaf cohomology map to the reduction is surjective. -/
theorem structureSheafH1_reduction_surjective
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsMinimalModel f]
    (genericFiberIso : C ≅
      Over.mk (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (h_gcd : specialFiberMultiplicityGcd f n components = 1)
    (h_red_sections : Function.Bijective (Scheme.Hom.globalSectionsMap
      (Scheme.reductionι (f.fiber (IsLocalRing.closedPoint R)) ≫
        f.fiberToSpecResidueField (IsLocalRing.closedPoint R)))) :
    Function.Surjective
      (reductionCohomologyMap
        (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)) 1).hom := sorry

/-- For a minimal model of a smooth projective curve over the fraction field of a discrete
valuation ring, with multiplicity gcd one and constant global functions on the reduced special
fibre, a nonreduced special fibre has a nontrivial kernel in its degree-one reduction
cohomology map. -/
theorem structureSheafH1_reduction_kernel_nontrivial
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsMinimalModel f]
    (genericFiberIso : C ≅
      Over.mk (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (h_gcd : specialFiberMultiplicityGcd f n components = 1)
    (h_red_sections : Function.Bijective (Scheme.Hom.globalSectionsMap
      (Scheme.reductionι (f.fiber (IsLocalRing.closedPoint R)) ≫
        f.fiberToSpecResidueField (IsLocalRing.closedPoint R))))
    (h_nonreduced : ¬ IsReduced (f.fiber (IsLocalRing.closedPoint R))) :
    LinearMap.ker
        (reductionCohomologyMap
          (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)) 1).hom ≠ ⊥ := sorry

end AlgebraicGeometry.Scheme.Hom
