/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.SpecialFiber

open AlgebraicGeometry AlgebraicGeometry.Scheme.Hom CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Definition 55.11.4: in Situation 55.9.3, `NumericalType.ofSpecialFiber` is
the numerical type associated to the model `X`. -/
@[stacks 0CA5] #check (NumericalType.ofSpecialFiber :
  ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅
      Over.mk (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (h_component_proper :
      ∀ i, IsProper (SpecialFiber.componentToResidueField f (components i)))
    (h_component_dimension :
      ∀ i, topologicalKrullDim (SpecialFiber.component f (components i)) ≤ 1),
    NumericalType)
