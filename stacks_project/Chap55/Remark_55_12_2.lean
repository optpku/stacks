/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Contraction.Genus

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Remark 55.12.2 -/
@[stacks 0CA8] #check
  (AlgebraicGeometry.IsContraction.componentGenusFormula :
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
      let sourceGenus : Fin (n + 1) → ℕ := fun i ↦
        Scheme.Hom.cohomologyFinrank
          (Scheme.Hom.SpecialFiber.component p (components i)).toSpecΓ
          (SheafOfModules.unit
            (Scheme.Hom.SpecialFiber.component p (components i)).ringCatSheaf :
            (Scheme.Hom.SpecialFiber.component p (components i)).Modules) 1
      let sourceWeight : Fin (n + 1) → ℕ := fun i ↦
        Scheme.Hom.SpecialFiber.componentWeight p (components i)
      let targetGenus : Fin n → ℕ := fun i ↦
        Scheme.Hom.cohomologyFinrank
          (Scheme.Hom.SpecialFiber.component p' (components' i)).toSpecΓ
          (SheafOfModules.unit
            (Scheme.Hom.SpecialFiber.component p' (components' i)).ringCatSheaf :
            (Scheme.Hom.SpecialFiber.component p' (components' i)).Modules) 1
      let targetWeight : Fin n → ℕ := fun i ↦
        Scheme.Hom.SpecialFiber.componentWeight p' (components' i)
      ∀ i : Fin n,
        (targetGenus i : ℚ) =
          (sourceWeight i.castSucc : ℚ) / (targetWeight i : ℚ) *
              ((sourceGenus i.castSucc : ℚ) - 1) + 1 +
            ((sourceForm (Pi.single i.castSucc 1)
                (Pi.single (Fin.last n) 1) : ℚ) ^ 2 -
              (sourceWeight (Fin.last n) : ℚ) *
                (sourceForm (Pi.single i.castSucc 1)
                  (Pi.single (Fin.last n) 1) : ℚ)) /
              (2 * (targetWeight i : ℚ) * (sourceWeight (Fin.last n) : ℚ)))
