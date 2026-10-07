module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.ExceptionalPair

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 55.9.11: two distinct intersecting exceptional components force a special fibre
with two multiplicity-one projective lines whose scheme-theoretic intersection is the
closed-point residue-field spectrum, and generic genus zero. -/
@[stacks 0C6A] #check (AlgebraicGeometry.Scheme.Hom.exceptionalPair_n_eq_two :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (π : R) (hπ : Irreducible π) (C : SchemeOverField K)
      [Curve C] [Smooth C.hom] [Projective C.hom]
      (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
      [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (n : ℕ)
      (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
      (i j : Fin n) (hij : i ≠ j)
      [IsExceptionalCurveFirstKind (f.specialFiberComponent (components i))]
      [IsExceptionalCurveFirstKind (f.specialFiberComponent (components j))]
      (h_intersects : Set.Nonempty
        ((components i : Set (f.fiber (IsLocalRing.closedPoint R))) ∩
          (components j : Set (f.fiber (IsLocalRing.closedPoint R))))),
      n = 2)

#check (AlgebraicGeometry.Scheme.Hom.exceptionalPair_multiplicity_eq_one :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (π : R) (hπ : Irreducible π) (C : SchemeOverField K)
      [Curve C] [Smooth C.hom] [Projective C.hom]
      (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
      [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (n : ℕ)
      (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
      (i j : Fin n) (hij : i ≠ j)
      [IsExceptionalCurveFirstKind (f.specialFiberComponent (components i))]
      [IsExceptionalCurveFirstKind (f.specialFiberComponent (components j))]
      (h_intersects : Set.Nonempty
        ((components i : Set (f.fiber (IsLocalRing.closedPoint R))) ∩
          (components j : Set (f.fiber (IsLocalRing.closedPoint R))))),
      ∀ r : Fin n, f.specialFiberMultiplicities (components r) = 1)

#check (AlgebraicGeometry.Scheme.Hom.exceptionalPair_components_iso_projectiveLine :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (π : R) (hπ : Irreducible π) (C : SchemeOverField K)
      [Curve C] [Smooth C.hom] [Projective C.hom]
      (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
      [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (n : ℕ)
      (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
      (i j : Fin n) (hij : i ≠ j)
      [IsExceptionalCurveFirstKind (f.specialFiberComponent (components i))]
      [IsExceptionalCurveFirstKind (f.specialFiberComponent (components j))]
      (h_intersects : Set.Nonempty
        ((components i : Set (f.fiber (IsLocalRing.closedPoint R))) ∩
          (components j : Set (f.fiber (IsLocalRing.closedPoint R))))),
      ∀ r : Fin n,
        Nonempty (Over.mk
          (AlgebraicGeometry.Scheme.Hom.SpecialFiber.componentToResidueField f (components r)) ≅
          ProjectiveSpace.schemeOver
            ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) 1))

#check (AlgebraicGeometry.Scheme.Hom.exceptionalPair_intersection_iso_spec :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (π : R) (hπ : Irreducible π) (C : SchemeOverField K)
      [Curve C] [Smooth C.hom] [Projective C.hom]
      (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
      [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (n : ℕ)
      (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
      (i j : Fin n) (hij : i ≠ j)
      [IsExceptionalCurveFirstKind (f.specialFiberComponent (components i))]
      [IsExceptionalCurveFirstKind (f.specialFiberComponent (components j))]
      (h_intersects : Set.Nonempty
        ((components i : Set (f.fiber (IsLocalRing.closedPoint R))) ∩
          (components j : Set (f.fiber (IsLocalRing.closedPoint R))))),
      Nonempty (Over.mk
        (pullback.fst (Scheme.Hom.SpecialFiber.componentInclusion f (components i))
            (Scheme.Hom.SpecialFiber.componentInclusion f (components j)) ≫
          Scheme.Hom.SpecialFiber.componentToResidueField f (components i)) ≅
        Over.mk (𝟙 (Spec ((Spec (CommRingCat.of R)).residueField
          (IsLocalRing.closedPoint R))))))

#check (AlgebraicGeometry.Scheme.Hom.exceptionalPair_genus_eq_zero :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (π : R) (hπ : Irreducible π) (C : SchemeOverField K)
      [Curve C] [Smooth C.hom] [Projective C.hom]
      (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
      [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (n : ℕ)
      (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
      (i j : Fin n) (hij : i ≠ j)
      [IsExceptionalCurveFirstKind (f.specialFiberComponent (components i))]
      [IsExceptionalCurveFirstKind (f.specialFiberComponent (components j))]
      (h_intersects : Set.Nonempty
        ((components i : Set (f.fiber (IsLocalRing.closedPoint R))) ∩
          (components j : Set (f.fiber (IsLocalRing.closedPoint R))))),
      SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections = 0)
