/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Regular

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.SpecialFiber

/-- For a regular proper model over a discrete valuation ring, the genus of its smooth generic
fibre is determined by the multiplicities, residue-field degrees, component genera, and
self-intersection degrees of the reduced special-fibre components. -/
theorem genus_eq_specialFiber_formula
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    let h_component_proper : ∀ i, IsProper (componentToResidueField f (components i)) :=
      fun i => inferInstance
    let h_component_dimension :
        ∀ i, topologicalKrullDim (component f (components i)) ≤ 1 :=
      fun i => component_dimension_le_one C h_globalSections f genericFiberIso n components i
    (SchemeOverField.genus C
      (AlgebraicGeometry.topologicalKrullDim_eq_one C) h_globalSections : ℚ) =
      1 + ∑ i, (f.specialFiberMultiplicities (components i) : ℚ) *
        ((@Module.finrank
            ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
            (Scheme.Hom.globalSectionsAlg
              (componentToResidueField f (components i)))
            inferInstance inferInstance
            (@Algebra.toModule
              ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
              (Scheme.Hom.globalSectionsAlg
                (componentToResidueField f (components i)))
              inferInstance inferInstance
              (Scheme.Hom.globalSectionsAlgebra
                (componentToResidueField f (components i)))) : ℚ) *
          ((Scheme.Hom.cohomologyFinrank
            (component f (components i)).toSpecΓ
            (SheafOfModules.unit
              (component f (components i)).ringCatSheaf :
              (component f (components i)).Modules) 1 : ℚ) - 1) -
        (componentDegree f (components i) (h_component_proper i)
          (h_component_dimension i)
          ((Scheme.Modules.pullback (componentInclusion f (components i))).obj
            (f.specialFiberComponent (components i)).associatedSheaf) : ℚ) / 2) := sorry

end AlgebraicGeometry.Scheme.Hom.SpecialFiber
