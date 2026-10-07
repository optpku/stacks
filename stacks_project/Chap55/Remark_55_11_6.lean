module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.NumericalType.Counterexamples

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators

/- Remark 55.11.6 (1): numerical types of negative genus exist. -/
@[stacks 0CA7] #check
  (NumericalType.negativeGenus_not_isSpecialFiberType :
    ∀ (T : NumericalType) (R K : Type) [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
      {X : Scheme} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
      [Scheme.Hom.FiniteType f] [IsProper f]
      [Scheme.Regular X]
      (h_generic : Smooth (pullback.snd f
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
        GeometricallyIntegral (pullback.snd f
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
        topologicalKrullDim (pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) : Scheme) = 1)
      (hgenus : T.genus < 0),
      ¬ T.IsSpecialFiberType R K f h_generic)
@[stacks 0CA7] #check
  (NumericalType.exists_negativeGenus : ∃ T : NumericalType, T.genus < 0)

/- Remark 55.11.6 (2): the one-component numerical type has the displayed data. -/
@[stacks 0CA7] #check
  (NumericalType.ModelCounterexample.single : NumericalType)
#check
  (NumericalType.ModelCounterexample.single_n :
    NumericalType.ModelCounterexample.single.n = 1)
#check
  (NumericalType.ModelCounterexample.single_multiplicity :
    ∀ i : Fin NumericalType.ModelCounterexample.single.n,
      NumericalType.ModelCounterexample.single.multiplicity i = 1)
#check
  (NumericalType.ModelCounterexample.single_intersection :
    ∀ i j : Fin NumericalType.ModelCounterexample.single.n,
      NumericalType.ModelCounterexample.single.intersection i j = 0)
#check
  (NumericalType.ModelCounterexample.single_weight :
    ∀ i : Fin NumericalType.ModelCounterexample.single.n,
      NumericalType.ModelCounterexample.single.weight i = 6)
#check
  (NumericalType.ModelCounterexample.single_componentGenus :
    ∀ i : Fin NumericalType.ModelCounterexample.single.n,
      NumericalType.ModelCounterexample.single.componentGenus i = 1)

/- Remark 55.11.6 (3): the one-component type is minimal and has genus one. -/
@[stacks 0CA7] #check
  (NumericalType.ModelCounterexample.single_isMinimal :
    NumericalType.ModelCounterexample.single.IsMinimal)
#check
  (NumericalType.ModelCounterexample.single_genus :
    NumericalType.ModelCounterexample.single.genus = 1)

/- Remark 55.11.6 (4): the two-component numerical type has the displayed data. -/
@[stacks 0CA7] #check
  (NumericalType.ModelCounterexample.pair : NumericalType)
#check
  (NumericalType.ModelCounterexample.pair_n :
    NumericalType.ModelCounterexample.pair.n = 2)
#check
  (NumericalType.ModelCounterexample.pair_multiplicity :
    ∀ i : Fin NumericalType.ModelCounterexample.pair.n,
      NumericalType.ModelCounterexample.pair.multiplicity i = 1)
#check
  (NumericalType.ModelCounterexample.pair_intersection :
    ∀ i j : Fin NumericalType.ModelCounterexample.pair.n,
      NumericalType.ModelCounterexample.pair.intersection i j = if i = j then -6 else 6)
#check
  (NumericalType.ModelCounterexample.pair_weight :
    ∀ i : Fin NumericalType.ModelCounterexample.pair.n,
      NumericalType.ModelCounterexample.pair.weight i = 6)
#check
  (NumericalType.ModelCounterexample.pair_componentGenus :
    ∀ i : Fin NumericalType.ModelCounterexample.pair.n,
      NumericalType.ModelCounterexample.pair.componentGenus i = 1)

/- Remark 55.11.6 (5): the two-component type is minimal and has genus seven. -/
@[stacks 0CA7] #check
  (NumericalType.ModelCounterexample.pair_isMinimal :
    NumericalType.ModelCounterexample.pair.IsMinimal)
#check
  (NumericalType.ModelCounterexample.pair_genus :
    NumericalType.ModelCounterexample.pair.genus = 7)

/- Remark 55.11.6 (6): the examples are excluded by the special-fibre realization API. -/
@[stacks 0CA7] #check
  (NumericalType.ModelCounterexample.single_not_isSpecialFiberType :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      {X : Scheme} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
      [Scheme.Hom.FiniteType f] [IsProper f]
      [Scheme.Regular X]
      (h_generic : Smooth (pullback.snd f
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
        GeometricallyIntegral (pullback.snd f
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
        topologicalKrullDim (pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) : Scheme) = 1),
      ¬ NumericalType.IsSpecialFiberType
        NumericalType.ModelCounterexample.single R K f h_generic)

#check
  (NumericalType.ModelCounterexample.pair_not_isSpecialFiberType :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      {X : Scheme} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
      [Scheme.Hom.FiniteType f] [IsProper f]
      [Scheme.Regular X]
      (h_generic : Smooth (pullback.snd f
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
        GeometricallyIntegral (pullback.snd f
          (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
        topologicalKrullDim (pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) : Scheme) = 1),
      ¬ NumericalType.IsSpecialFiberType
        NumericalType.ModelCounterexample.pair R K f h_generic)

/- Remark 55.11.6 (7): the gcd-one observation is only an informal observation. -/
/- If the gcd of the weights is one, this remark supplies no realizability theorem. -/
