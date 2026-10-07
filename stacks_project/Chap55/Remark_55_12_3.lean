module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Contraction.Genus
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Contraction.Weights
public import ReasLib.AlgebraicGeometry.NumericalType.ContractionComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumericalType
open scoped AlgebraicGeometry

universe u

/- Remark 55.12.3 (1): Geometric contraction preserves the surviving multiplicities. -/
@[stacks 0CA9] #check (@AlgebraicGeometry.IsContraction.componentImageAndMultiplicity :
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

/- Remark 55.12.3 (2): Geometric contraction has the numerical Schur-complement intersection formula. -/
@[stacks 0CA9] #check (@AlgebraicGeometry.IsContraction.intersectionFormula :
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

/- Remark 55.12.3 (3): The geometric genus uses the actual geometric weights in the same rational formula. -/
@[stacks 0CA9] #check (@AlgebraicGeometry.IsContraction.componentGenusFormula :
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

/- Remark 55.12.3 (4): Geometric weights are positive divisors of the original weights. -/
@[stacks 0CA9] #check (@AlgebraicGeometry.IsContraction.componentWeight_dvd_source :
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
    ∀ i : Fin n,
      0 < Scheme.Hom.SpecialFiber.componentWeight p' (components' i) ∧
        Scheme.Hom.SpecialFiber.componentWeight p' (components' i) ∣
          Scheme.Hom.SpecialFiber.componentWeight p (components i.castSucc))

/- Remark 55.12.3 (5): With incidence, the geometric weight also divides the exceptional weight (recorded erratum). -/
@[stacks 0CA9] #check (@AlgebraicGeometry.IsContraction.componentWeight_dvd_exceptional :
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
    ∀ i : Fin n,
      Set.Nonempty
        (((p.specialFiberComponent (components i.castSucc)).support : Set X) ∩
          ((p.specialFiberComponent (components (Fin.last n))).support : Set X)) →
        Scheme.Hom.SpecialFiber.componentWeight p' (components' i) ∣
          Scheme.Hom.SpecialFiber.componentWeight p (components (Fin.last n)))

/- Remark 55.12.3 (6): Numerical weights are maximal among positive divisors giving integral genus. -/
@[stacks 0CA9] #check (@NumericalType.contractMinusOne_weight_isGreatest :
  ∀ (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))) (i : Fin (T.n - 1)),
    IsGreatest {w : ℕ | 0 < w ∧ w ∣ T.weight (e i.castSucc) ∧
      ∃ g : ℤ, contractionGenus T (e i.castSucc) (e (Fin.last (T.n - 1))) w = (g : ℚ)}
      ((contractMinusOne T e hminus).weight i))

/- Remark 55.12.3 (7): The numerical natural genus satisfies the exact rational formula. -/
@[stacks 0CA9] #check (@NumericalType.contractMinusOne_genus_rational :
  ∀ (T : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1)))) (i : Fin (T.n - 1)),
    ((contractMinusOne T e hminus).componentGenus i : ℚ) =
      contractionGenus T (e i.castSucc) (e (Fin.last (T.n - 1)))
        ((contractMinusOne T e hminus).weight i))

/- Remark 55.12.3 (8): The concrete Picard comparison is injective for every dividing retained weight choice. -/
@[stacks 0CA9] #check (@NumericalType.contractionPicardMap_injective :
  ∀ (T U : NumericalType)
    (e : Fin (T.n - 1 + 1) ≃ Fin T.n) (f : Fin (T.n - 1) ≃ Fin U.n)
    (hminus : IsMinusOneIndex T.componentGenus T.weight T.intersection
      (e (Fin.last (T.n - 1))))
    (hw : ∀ i, U.weight (f i) ∣ T.weight (e i.castSucc))
    (ha : ∀ i j, U.intersection (f i) (f j) =
      T.intersection (e i.castSucc) (e j.castSucc) -
        T.intersection (e i.castSucc) (e (Fin.last (T.n - 1))) *
          T.intersection (e j.castSucc) (e (Fin.last (T.n - 1))) /
            T.intersection (e (Fin.last (T.n - 1))) (e (Fin.last (T.n - 1)))),
    Function.Injective (contractionPicardMap T U e f hminus hw ha))
