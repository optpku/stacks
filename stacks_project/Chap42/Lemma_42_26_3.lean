module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 42.26.3 (1): for a proper dominant morphism of integral schemes of equal relative
dimension, the pushforward of the divisor cycle of a pulled-back nonzero meromorphic section is
the function-field degree times its original divisor cycle. -/
@[stacks 02ST] #check
  (AlgebraicGeometry.AlgebraicCycle.map_divisor_pullback_of_proper :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      [AlgebraicGeometry.LocallyOfFiniteType Y.hom]
      [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsIntegral Y.left]
      (n : ℤ) (f : X ⟶ Y) [AlgebraicGeometry.IsProper f.left]
      [AlgebraicGeometry.IsDominant f.left]
      (hX : X.hom.relativeDimensionFunction δ (genericPoint X.left) = n)
      (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
      (ℒ : Y.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ]
      (s : Y.left.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0),
      AlgebraicGeometry.AlgebraicCycle.map f.left
          (X.hom.relativeDimensionFunction δ) (Y.hom.relativeDimensionFunction δ)
          (@AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionDivisorCycle X.left
            (AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian X.hom) inferInstance
            ((AlgebraicGeometry.Scheme.Modules.pullback f.left).obj ℒ) inferInstance
            (AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackMeromorphicSections
              f.left.toLRSHom
              (AlgebraicGeometry.Scheme.Hom.MeromorphicFunction.pullbackDefined_of_isIntegral_of_isDominant
                f.left) ℒ s)
            (AlgebraicGeometry.Scheme.Hom.MeromorphicFunction.pullbackSections_ne_zero_of_isDominant
              f.left ℒ s hs)) =
        (f.left.inducedFunctionFieldDegree : ℤ) •
          @AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionDivisorCycle Y.left
            (AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian Y.hom) inferInstance
            ℒ inferInstance s hs)

/- Lemma 42.26.3 (2): proper pushforward of first-Chern intersection with the fundamental
cycle equals the function-field degree times the corresponding intersection on the target. -/
@[stacks 02ST] #check
  (AlgebraicGeometry.ChowGroup.map_firstChernClassCap_fundamental :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      [AlgebraicGeometry.LocallyOfFiniteType Y.hom]
      [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsIntegral Y.left]
      (k : ℤ) (f : X ⟶ Y) [AlgebraicGeometry.IsProper f.left]
      [AlgebraicGeometry.IsDominant f.left]
      (hX : X.hom.relativeDimensionFunction δ (genericPoint X.left) = k + 1)
      (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = k + 1)
      (ℒ : Y.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ],
      AlgebraicGeometry.ChowGroup.map δ X Y f k
          (AlgebraicGeometry.Scheme.Modules.firstChernClassCap X.hom δ
            ((AlgebraicGeometry.Scheme.Modules.pullback f.left).obj ℒ) k
            (@AlgebraicGeometry.CycleGroup.fundamental X.left
              (AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (X.hom.relativeDimensionFunction δ) (k + 1))) =
        (f.left.inducedFunctionFieldDegree : ℤ) •
          AlgebraicGeometry.Scheme.Modules.firstChernClassCap Y.hom δ ℒ k
            (@AlgebraicGeometry.CycleGroup.fundamental Y.left
              (AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian Y.hom)
              (Y.hom.relativeDimensionFunction δ) (k + 1)))

/- Lemma 42.26.3 (3): the degree multiple of first-Chern intersection on the target is first
Chern intersection with the pushforward of the source fundamental cycle. -/
@[stacks 02ST] #check
  (AlgebraicGeometry.ChowGroup.firstChernClassCap_map_fundamental :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.UniversallyCatenary S]
      (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [AlgebraicGeometry.LocallyOfFiniteType X.hom]
      [AlgebraicGeometry.LocallyOfFiniteType Y.hom]
      [AlgebraicGeometry.IsIntegral X.left] [AlgebraicGeometry.IsIntegral Y.left]
      (k : ℤ) (f : X ⟶ Y) [AlgebraicGeometry.IsProper f.left]
      [AlgebraicGeometry.IsDominant f.left]
      (hX : X.hom.relativeDimensionFunction δ (genericPoint X.left) = k + 1)
      (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = k + 1)
      (ℒ : Y.left.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ],
      (f.left.inducedFunctionFieldDegree : ℤ) •
          AlgebraicGeometry.Scheme.Modules.firstChernClassCap Y.hom δ ℒ k
            (@AlgebraicGeometry.CycleGroup.fundamental Y.left
              (AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian Y.hom)
              (Y.hom.relativeDimensionFunction δ) (k + 1)) =
        AlgebraicGeometry.Scheme.Modules.firstChernClassCap Y.hom δ ℒ k
          (AlgebraicGeometry.CycleGroup.mapHom f.left
            (X.hom.relativeDimensionFunction δ) (Y.hom.relativeDimensionFunction δ) (k + 1)
            (@AlgebraicGeometry.CycleGroup.fundamental X.left
              (AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (X.hom.relativeDimensionFunction δ) (k + 1))))
