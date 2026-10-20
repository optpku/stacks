module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.PrimitiveDivisor
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The reduced special fibre of a regular proper flat model of a smooth curve whose
global functions are its base field admits a finite chain of effective Cartier divisors
ending at the primitive special-fibre divisor. Each step adds one reduced irreducible
component, and the global-sections algebra of every stage is a field finite-dimensional
over the residue field. -/
theorem exists_effectiveCartierDivisorSequence
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : AlgebraicGeometry.SchemeOverField K) [AlgebraicGeometry.Curve C]
    [Smooth C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    ∃ m : ℕ, ∃ Z : Fin (m + 1) → X.IdealSheafData, ∃ step : Fin m → Fin n,
      ∃ fiberLift : ∀ j, (Z j).subscheme ⟶ f.fiber (IsLocalRing.closedPoint R),
        Z 0 = Scheme.IdealSheafData.vanishingIdeal f.specialFiberIdeal.support ∧
        Z (Fin.last m) = primitiveSpecialFiberDivisor f n components ∧
        (∀ j, IsEffectiveCartierDivisor (Z j).subschemeι) ∧
        (∀ j, fiberLift j ≫ f.fiberι (IsLocalRing.closedPoint R) = (Z j).subschemeι) ∧
        (∀ j : Fin m,
          Z j.succ ≤ Z j.castSucc ∧
            Z j.succ = effectiveCartierDivisorSum (Z j.castSucc)
              (f.specialFiberComponent (components (step j)))) ∧
        ∀ j, IsField (Scheme.Hom.globalSectionsAlg
          (fiberLift j ≫ f.fiberToSpecResidueField (IsLocalRing.closedPoint R))) ∧
        FiniteDimensional
          ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
          (Scheme.Hom.globalSectionsAlg
            (fiberLift j ≫ f.fiberToSpecResidueField (IsLocalRing.closedPoint R)) :
            CommAlgCat ((Spec (CommRingCat.of R)).residueField
              (IsLocalRing.closedPoint R))) := sorry

end AlgebraicGeometry.Scheme.Hom
