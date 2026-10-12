/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.CurveDegree
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Euler characteristics on special-fibre components
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For effective Cartier divisors `D` and `D'` on a regular proper model, if `D'` is obtained by
adding a reduced special-fibre component to `D`, the difference of their Euler characteristics
is the Euler characteristic of the negative sheaf of `D` pulled back to that component. -/
theorem eulerCharacteristic_sub_eq_restriction
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : AlgebraicGeometry.SchemeOverField K) [AlgebraicGeometry.Curve C]
    [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (D D' : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    [IsEffectiveCartierDivisor D'.subschemeι]
    (i : Fin n)
    (h_sum : D' = effectiveCartierDivisorSum D (f.specialFiberComponent (components i)))
    (D_to_fiber : D.subscheme ⟶ f.fiber (IsLocalRing.closedPoint R))
    (h_D_to_fiber : D_to_fiber ≫ f.fiberι (IsLocalRing.closedPoint R) = D.subschemeι)
    (D'_to_fiber : D'.subscheme ⟶ f.fiber (IsLocalRing.closedPoint R))
    (h_D'_to_fiber : D'_to_fiber ≫ f.fiberι (IsLocalRing.closedPoint R) = D'.subschemeι)
    [h_D_proper : IsProper
      (D_to_fiber ≫ f.fiberToSpecResidueField (IsLocalRing.closedPoint R))]
    [h_D'_proper : IsProper
      (D'_to_fiber ≫ f.fiberToSpecResidueField (IsLocalRing.closedPoint R))]
    (h_component_proper : IsProper
      (SpecialFiber.componentToResidueField f (components i)))
    [(SheafOfModules.unit D.subscheme.ringCatSheaf : D.subscheme.Modules).IsCoherent]
    [(SheafOfModules.unit D'.subscheme.ringCatSheaf : D'.subscheme.Modules).IsCoherent]
    [((Scheme.Modules.pullback (SpecialFiber.componentInclusion f (components i))).obj
      D.negSheaf).IsCoherent] :
    @eulerCharacteristic _ _ _
          (D'_to_fiber ≫ f.fiberToSpecResidueField (IsLocalRing.closedPoint R))
          h_D'_proper
          (SheafOfModules.unit D'.subscheme.ringCatSheaf : D'.subscheme.Modules)
          inferInstance -
        @eulerCharacteristic _ _ _
          (D_to_fiber ≫ f.fiberToSpecResidueField (IsLocalRing.closedPoint R))
          h_D_proper
          (SheafOfModules.unit D.subscheme.ringCatSheaf : D.subscheme.Modules)
          inferInstance =
      @eulerCharacteristic _ _ _
        (SpecialFiber.componentToResidueField f (components i))
        h_component_proper
        ((Scheme.Modules.pullback (SpecialFiber.componentInclusion f (components i))).obj
          D.negSheaf)
        inferInstance := sorry

/-- On a reduced special-fibre component of dimension at most one, the Euler characteristic of the
negative sheaf of an effective Cartier divisor is minus its degree plus the Euler characteristic of
the component's structure sheaf. -/
theorem restrictionEulerCharacteristic_eq_neg_componentDegree_add
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : AlgebraicGeometry.SchemeOverField K) [AlgebraicGeometry.Curve C]
    [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (h_component_proper : ∀ i,
      IsProper (SpecialFiber.componentToResidueField f (components i)))
    (h_component_dimension : ∀ i,
      topologicalKrullDim (SpecialFiber.component f (components i)) ≤ 1)
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι]
    (i : Fin n)
    [((Scheme.Modules.pullback (SpecialFiber.componentInclusion f (components i))).obj
      D.negSheaf).IsCoherent]
    [(SheafOfModules.unit (SpecialFiber.component f (components i)).ringCatSheaf :
      (SpecialFiber.component f (components i)).Modules).IsCoherent] :
    @eulerCharacteristic _ _ _
        (SpecialFiber.componentToResidueField f (components i))
        (h_component_proper i)
        ((Scheme.Modules.pullback (SpecialFiber.componentInclusion f (components i))).obj
          D.negSheaf)
        inferInstance =
      -SpecialFiber.componentDegree f (components i) (h_component_proper i)
          (h_component_dimension i)
          ((Scheme.Modules.pullback (SpecialFiber.componentInclusion f (components i))).obj
            D.associatedSheaf) +
        @eulerCharacteristic _ _ _
          (SpecialFiber.componentToResidueField f (components i))
          (h_component_proper i)
          (SheafOfModules.unit (SpecialFiber.component f (components i)).ringCatSheaf :
            (SpecialFiber.component f (components i)).Modules)
          inferInstance := sorry

end AlgebraicGeometry.Scheme.Hom
