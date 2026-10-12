/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.IntersectionPairing
public import ReasLib.LinearAlgebra.Matrix.NegativeSemidefinite

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry BigOperators

universe u

namespace AlgebraicGeometry.Scheme.Hom.SpecialFiber

/-- Distinct irreducible components of a regular proper model have nonnegative intersection,
with vanishing exactly when their underlying closed subsets are disjoint. -/
theorem intersection_offDiagonal_nonnegative_of_regularModel
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    let h_component_proper : ∀ i, IsProper (componentToResidueField f (components i)) :=
      fun i ↦ instIsProperComponentToResidueField f (components i)
    let h_component_dimension : ∀ i, topologicalKrullDim (component f (components i)) ≤ 1 :=
      fun i ↦ component_dimension_le_one C h_globalSections f genericFiberIso n components i
    let B := intersectionForm f n components h_component_proper h_component_dimension
    ∀ i j : Fin n, i ≠ j →
      0 ≤ B (Pi.single i 1) (Pi.single j 1) ∧
        (B (Pi.single i 1) (Pi.single j 1) = 0 ↔
          Disjoint (components i).1 (components j).1) := sorry

/-- The special-fibre multiplicity vector is orthogonal to every component of a regular
proper model. -/
theorem weighted_intersection_eq_zero_of_regularModel
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    let h_component_proper : ∀ i, IsProper (componentToResidueField f (components i)) :=
      fun i ↦ instIsProperComponentToResidueField f (components i)
    let h_component_dimension : ∀ i, topologicalKrullDim (component f (components i)) ≤ 1 :=
      fun i ↦ component_dimension_le_one C h_globalSections f genericFiberIso n components i
    let B := intersectionForm f n components h_component_proper h_component_dimension
    ∀ j : Fin n,
      B (fun i ↦ (f.specialFiberMultiplicities (components i) : ℤ)) (Pi.single j 1) = 0 := sorry

/-- No nonempty proper collection of components of a regular proper model is disjoint from
all components in its complement. -/
theorem intersection_no_disconnected_subset_of_regularModel
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    let h_component_proper : ∀ i, IsProper (componentToResidueField f (components i)) :=
      fun i ↦ instIsProperComponentToResidueField f (components i)
    let h_component_dimension : ∀ i, topologicalKrullDim (component f (components i)) ≤ 1 :=
      fun i ↦ component_dimension_le_one C h_globalSections f genericFiberIso n components i
    let B := intersectionForm f n components h_component_proper h_component_dimension
    ¬ ∃ I : Set (Fin n), I.Nonempty ∧ I ≠ Set.univ ∧
      ∀ i ∈ I, ∀ j ∉ I, B (Pi.single i 1) (Pi.single j 1) = 0 := sorry

/-- The geometric intersection form of a regular proper model is nonpositive on every
integral coefficient vector. -/
theorem intersectionForm_nonpos_of_regularModel
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    let h_component_proper : ∀ i, IsProper (componentToResidueField f (components i)) :=
      fun i ↦ instIsProperComponentToResidueField f (components i)
    let h_component_dimension : ∀ i, topologicalKrullDim (component f (components i)) ≤ 1 :=
      fun i ↦ component_dimension_le_one C h_globalSections f genericFiberIso n components i
    let B := intersectionForm f n components h_component_proper h_component_dimension
    ∀ a : Fin n → ℤ, B a a ≤ 0 := sorry

/-- Equality in the nonpositivity of the geometric intersection form holds exactly for rational
multiples of the special-fibre multiplicity vector. -/
theorem intersectionForm_eq_zero_iff_of_regularModel
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    let h_component_proper : ∀ i, IsProper (componentToResidueField f (components i)) :=
      fun i ↦ instIsProperComponentToResidueField f (components i)
    let h_component_dimension : ∀ i, topologicalKrullDim (component f (components i)) ≤ 1 :=
      fun i ↦ component_dimension_le_one C h_globalSections f genericFiberIso n components i
    let B := intersectionForm f n components h_component_proper h_component_dimension
    ∀ a : Fin n → ℤ,
      B a a = 0 ↔ ∃ q : ℚ, ∀ i,
        (a i : ℚ) = q * (f.specialFiberMultiplicities (components i) : ℚ) := sorry

end AlgebraicGeometry.Scheme.Hom.SpecialFiber
