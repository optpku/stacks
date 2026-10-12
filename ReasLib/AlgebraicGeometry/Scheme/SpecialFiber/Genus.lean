/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.DivisorSequence
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The primitive special-fibre divisor of a regular proper flat model of a smooth curve
with no additional global functions has dimension one. -/
theorem primitiveSpecialFiber_dimension_eq_one
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom]
    (h_globalSections : Function.Bijective (globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    topologicalKrullDim (primitiveSpecialFiberDivisor f n components).subscheme = 1 := sorry

/-- Global functions on the primitive special-fibre divisor of a regular proper flat
model of a smooth curve with no additional global functions form a field finite-dimensional
over the residue field. -/
theorem primitiveSpecialFiber_globalSections_isField_and_finite
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom]
    (h_globalSections : Function.Bijective (globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    IsField (Scheme.globalSectionsRing (primitiveSpecialFiberDivisor f n components).subscheme) ∧
      FiniteDimensional
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
        (globalSectionsAlg (primitiveSpecialFiberToResidueField f n components) :
          CommAlgCat ((Spec (CommRingCat.of R)).residueField
            (IsLocalRing.closedPoint R))) := sorry

/-- For a regular proper flat model of a smooth curve with no additional global functions,
one minus the generic genus is the product of the gcd of the special-fibre multiplicities,
the residue-field degree of the global functions on the primitive divisor, and one minus
the genus of that divisor over its global-functions field. -/
theorem genusFormula_primitiveSpecialFiber
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom]
    (h_globalSections : Function.Bijective (globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    (1 : ℤ) - (cohomologyFinrank C.hom
      (SheafOfModules.unit C.left.ringCatSheaf : C.left.Modules) 1 : ℤ) =
      (specialFiberMultiplicityGcd f n components : ℤ) *
        (Module.finrank
          ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
          (globalSectionsAlg (primitiveSpecialFiberToResidueField f n components) :
            CommAlgCat ((Spec (CommRingCat.of R)).residueField
              (IsLocalRing.closedPoint R))) : ℤ) *
        ((1 : ℤ) - (cohomologyFinrank
          (primitiveSpecialFiberDivisor f n components).subscheme.toSpecΓ
          (SheafOfModules.unit (primitiveSpecialFiberDivisor f n components).subscheme.ringCatSheaf :
            (primitiveSpecialFiberDivisor f n components).subscheme.Modules) 1 : ℤ)) := sorry

end AlgebraicGeometry.Scheme.Hom
