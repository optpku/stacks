module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ExceptionalCurve
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Genus

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
variable [h_projective : Projective C.hom]
variable (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable [h_flat : Flat f] [h_finiteType : FiniteType f] [h_proper : IsProper f]
variable [h_regular : Scheme.Regular X]
variable (genericFiberIso : C ≅ Over.mk
  (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
variable (n : ℕ)
variable (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
variable (i j : Fin n) (hij : i ≠ j)
variable [h_i_exceptional : IsExceptionalCurveFirstKind
  (f.specialFiberComponent (components i))]
variable [h_j_exceptional : IsExceptionalCurveFirstKind
  (f.specialFiberComponent (components j))]
variable (h_intersects : Set.Nonempty
  ((components i : Set (f.fiber (IsLocalRing.closedPoint R))) ∩
    (components j : Set (f.fiber (IsLocalRing.closedPoint R)))))

include h_commRing h_domain h_dvr h_field h_algebra h_fractionRing hπ h_curve h_smooth
  h_projective h_globalSections h_flat h_finiteType h_proper h_regular genericFiberIso hij
  h_i_exceptional h_j_exceptional h_intersects

/-- Two distinct intersecting exceptional components of the special fibre of a regular
proper flat model of a smooth projective curve with no additional global functions force
the special fibre to have exactly two irreducible components. -/
theorem exceptionalPair_n_eq_two : n = 2 := sorry

/-- If two distinct exceptional components of the special fibre of a regular proper flat
model of a smooth projective curve with no additional global functions intersect, every
special-fibre component has multiplicity one. -/
theorem exceptionalPair_multiplicity_eq_one :
    ∀ r : Fin n, f.specialFiberMultiplicities (components r) = 1 := sorry

/-- If two distinct exceptional components of the special fibre of a regular proper flat
model of a smooth projective curve with no additional global functions intersect, every
special-fibre component is a projective line over the closed-point residue field. -/
theorem exceptionalPair_components_iso_projectiveLine :
    ∀ r : Fin n,
      Nonempty (Over.mk (SpecialFiber.componentToResidueField f (components r)) ≅
        ProjectiveSpace.schemeOver
          ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) 1) := sorry

/-- Two distinct intersecting exceptional components of the special fibre of a regular
proper flat model of a smooth projective curve with no additional global functions have
scheme-theoretic intersection isomorphic over the closed-point residue field to its spectrum. -/
theorem exceptionalPair_intersection_iso_spec :
    Nonempty (Over.mk
      (pullback.fst (SpecialFiber.componentInclusion f (components i))
          (SpecialFiber.componentInclusion f (components j)) ≫
        SpecialFiber.componentToResidueField f (components i)) ≅
      Over.mk (𝟙 (Spec ((Spec (CommRingCat.of R)).residueField
        (IsLocalRing.closedPoint R))))) := sorry

/-- A smooth projective curve with no additional global functions has genus zero if its
regular proper flat model has two distinct intersecting exceptional special-fibre
components. -/
theorem exceptionalPair_genus_eq_zero :
    SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections = 0 := sorry

end

end AlgebraicGeometry.Scheme.Hom
