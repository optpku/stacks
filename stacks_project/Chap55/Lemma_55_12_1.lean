module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Contraction

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsContraction

/- Lemma 55.12.1 (1): contracting the last exceptional component produces a regular proper model
with one fewer special-fibre component. -/
@[stacks 0C6C] #check
  (AlgebraicGeometry.IsContraction.targetModel :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
      (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
      {X X' : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
      [Flat p] [Scheme.Hom.FiniteType p] [IsProper p] [Scheme.Regular X]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (n : ℕ)
      (components : Fin (n + 1) ≃
        irreducibleComponents (p.fiber (IsLocalRing.closedPoint R)))
      [IsNoetherian X]
      [IsExceptionalCurveFirstKind
        (p.specialFiberComponent (components (Fin.last n)))]
      (b : X ⟶ X') (x : closedPoints X')
      (hb : IsContraction
        (p.specialFiberComponent (components (Fin.last n))) b x),
      ∃ (p' : X' ⟶ Spec (CommRingCat.of R))
        (genericFiberIso' : C ≅ Over.mk
          (pullback.snd p' (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
        (components' : Fin n ≃
          irreducibleComponents (p'.fiber (IsLocalRing.closedPoint R))),
        b ≫ p' = p ∧ IsNoetherian X' ∧ Flat p' ∧
          Scheme.Hom.FiniteType p' ∧ IsProper p' ∧ Scheme.Regular X')

/- Lemma 55.12.1 (2): surviving target components are the scheme-theoretic images of the source
components, with unchanged multiplicities. -/
@[stacks 0C6C] #check
  (AlgebraicGeometry.IsContraction.componentImageAndMultiplicity :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
      (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
      {X X' : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
      [Flat p] [Scheme.Hom.FiniteType p] [IsProper p] [Scheme.Regular X]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (n : ℕ)
      (components : Fin (n + 1) ≃
        irreducibleComponents (p.fiber (IsLocalRing.closedPoint R)))
      [IsNoetherian X]
      [IsExceptionalCurveFirstKind
        (p.specialFiberComponent (components (Fin.last n)))]
      (b : X ⟶ X') (x : closedPoints X')
      (hb : IsContraction
        (p.specialFiberComponent (components (Fin.last n))) b x)
      (p' : X' ⟶ Spec (CommRingCat.of R))
      [IsNoetherian X'] [Flat p'] [Scheme.Hom.FiniteType p'] [IsProper p']
      [Scheme.Regular X']
      (genericFiberIso' : C ≅ Over.mk
        (pullback.snd p' (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (h_over : b ≫ p' = p),
      ∃ (components' : Fin n ≃
        irreducibleComponents (p'.fiber (IsLocalRing.closedPoint R))),
        ∀ i : Fin n,
          (p.specialFiberComponent (components i.castSucc)).map b =
              p'.specialFiberComponent (components' i) ∧
            p'.specialFiberMultiplicities (components' i) =
              p.specialFiberMultiplicities (components i.castSucc))

/- Lemma 55.12.1 (3): the geometric intersection form changes by the Schur complement of the
exceptional component's self-intersection. -/
@[stacks 0C6C] #check
  (AlgebraicGeometry.IsContraction.intersectionFormula :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
      (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
      {X X' : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
      [Flat p] [Scheme.Hom.FiniteType p] [IsProper p] [Scheme.Regular X]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (n : ℕ)
      (components : Fin (n + 1) ≃
        irreducibleComponents (p.fiber (IsLocalRing.closedPoint R)))
      [IsNoetherian X]
      [IsExceptionalCurveFirstKind
        (p.specialFiberComponent (components (Fin.last n)))]
      (b : X ⟶ X') (x : closedPoints X')
      (hb : IsContraction
        (p.specialFiberComponent (components (Fin.last n))) b x)
      (p' : X' ⟶ Spec (CommRingCat.of R))
      [IsNoetherian X'] [Flat p'] [Scheme.Hom.FiniteType p'] [IsProper p']
      [Scheme.Regular X']
      (genericFiberIso' : C ≅ Over.mk
        (pullback.snd p' (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (components' : Fin n ≃
        irreducibleComponents (p'.fiber (IsLocalRing.closedPoint R)))
      (h_over : b ≫ p' = p)
      (h_image : ∀ i : Fin n,
        (p.specialFiberComponent (components i.castSucc)).map b =
          p'.specialFiberComponent (components' i)),
      let sourceProper : ∀ i, IsProper
          (Scheme.Hom.SpecialFiber.componentToResidueField p (components i)) :=
        fun i ↦ Scheme.Hom.SpecialFiber.instIsProperComponentToResidueField p
          (components i)
      let sourceDimension : ∀ i, topologicalKrullDim
          (Scheme.Hom.SpecialFiber.component p (components i)) ≤ 1 :=
        fun i ↦ Scheme.Hom.SpecialFiber.component_dimension_le_one C h_globalSections p
          genericFiberIso (n + 1) components i
      let targetProper : ∀ i, IsProper
          (Scheme.Hom.SpecialFiber.componentToResidueField p' (components' i)) :=
        fun i ↦ Scheme.Hom.SpecialFiber.instIsProperComponentToResidueField p'
          (components' i)
      let targetDimension : ∀ i, topologicalKrullDim
          (Scheme.Hom.SpecialFiber.component p' (components' i)) ≤ 1 :=
        fun i ↦ Scheme.Hom.SpecialFiber.component_dimension_le_one C h_globalSections p'
          genericFiberIso' n components' i
      let sourceForm := Scheme.Hom.SpecialFiber.intersectionForm p (n + 1) components
        sourceProper sourceDimension
      let targetForm := Scheme.Hom.SpecialFiber.intersectionForm p' n components'
        targetProper targetDimension
      ∀ i j : Fin n,
        (targetForm (Pi.single i 1) (Pi.single j 1) : ℚ) =
          (sourceForm (Pi.single i.castSucc 1) (Pi.single j.castSucc 1) : ℚ) -
            (sourceForm (Pi.single i.castSucc 1) (Pi.single (Fin.last n) 1) : ℚ) *
              (sourceForm (Pi.single j.castSucc 1) (Pi.single (Fin.last n) 1) : ℚ) /
                (sourceForm (Pi.single (Fin.last n) 1)
                  (Pi.single (Fin.last n) 1) : ℚ))

/- Lemma 55.12.1 (4): when a surviving component meets the exceptional component, global
sections on its image map to the global sections of both source components. -/
@[stacks 0C6C] #check
  (AlgebraicGeometry.IsContraction.globalSectionsMaps :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
      (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
      {X X' : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
      [Flat p] [Scheme.Hom.FiniteType p] [IsProper p] [Scheme.Regular X]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (n : ℕ)
      (components : Fin (n + 1) ≃
        irreducibleComponents (p.fiber (IsLocalRing.closedPoint R)))
      [IsNoetherian X]
      [IsExceptionalCurveFirstKind
        (p.specialFiberComponent (components (Fin.last n)))]
      (b : X ⟶ X') (x : closedPoints X')
      (hb : IsContraction
        (p.specialFiberComponent (components (Fin.last n))) b x),
      ∀ i : Fin n,
        Set.Nonempty
            (((p.specialFiberComponent (components i.castSucc)).support : Set X) ∩
              ((p.specialFiberComponent (components (Fin.last n))).support : Set X)) →
          Nonempty
              (Scheme.globalSectionsRing
                  (((p.specialFiberComponent (components i.castSucc)).map b).subscheme) ⟶
                Scheme.globalSectionsRing
                  ((p.specialFiberComponent (components i.castSucc)).subscheme)) ∧
            Nonempty
              (Scheme.globalSectionsRing
                  (((p.specialFiberComponent (components i.castSucc)).map b).subscheme) ⟶
                Scheme.globalSectionsRing
                  ((p.specialFiberComponent (components (Fin.last n))).subscheme)))

end AlgebraicGeometry.IsContraction
