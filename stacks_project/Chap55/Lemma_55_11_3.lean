/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.SpecialFiber
public import stacks_project.Chap55.Definition_55_3_1_NumericalType
public import stacks_project.Chap55.Definition_55_3_4_Genus
public import stacks_project.Chap55.Lemma_55_11_2

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Hom CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

namespace NumericalType

/- Lemma 55.11.3 (1): in Situation 55.9.3, the special-fibre data determine a numerical type. -/
@[stacks 0CA4] #check (NumericalType.ofSpecialFiber :
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

/- Lemma 55.11.3 (2): the genus of the special-fibre numerical type equals the genus of the generic curve. -/
@[stacks 0CA4] #check (NumericalType.ofSpecialFiber_genus_eq :
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
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))),
    (NumericalType.ofSpecialFiber R K π hπ C h_globalSections f genericFiberIso n
      components (fun i ↦ inferInstance)
        (fun i ↦ SpecialFiber.component_dimension_le_one
          C h_globalSections f genericFiberIso n components i)).genus =
      (SchemeOverField.genus C
        (AlgebraicGeometry.topologicalKrullDim_eq_one C) h_globalSections : ℤ))

end NumericalType
