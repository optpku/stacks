/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Reduction

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 55.11.8 (1): In Situation 55.9.3, for a minimal model with multiplicity gcd one
and constant global functions on the reduced special fibre, the degree-one structure-sheaf
cohomology map from the special fibre to its reduction is surjective. -/
@[stacks 0CE9] #check
  (AlgebraicGeometry.Scheme.Hom.structureSheafH1_reduction_surjective :
    ∀
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
        f.fiberToSpecResidueField (IsLocalRing.closedPoint R)))),
    Function.Surjective
      (reductionCohomologyMap
        (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)) 1).hom)

/- Lemma 55.11.8 (2): under the same hypotheses, if the special fibre is nonreduced, the
degree-one reduction cohomology map has a nontrivial kernel. -/
@[stacks 0CE9] #check
  (AlgebraicGeometry.Scheme.Hom.structureSheafH1_reduction_kernel_nontrivial :
    ∀
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
    (h_nonreduced : ¬ IsReduced (f.fiber (IsLocalRing.closedPoint R))),
    LinearMap.ker
        (reductionCohomologyMap
          (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)) 1).hom ≠ ⊥)

end AlgebraicGeometry.Scheme.Hom
