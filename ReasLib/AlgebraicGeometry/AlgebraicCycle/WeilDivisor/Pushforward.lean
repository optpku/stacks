/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Principal.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.WeilDivisor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree

/-!
# Proper pushforward of divisor cycles

This file relates proper pushforward of the divisor cycle of a pulled-back meromorphic section
to multiplication by the degree of the induced extension of function fields.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

/-- For a proper dominant morphism of integral schemes of equal relative dimension, the
pushforward of the divisor cycle of a pulled-back nonzero meromorphic section is the
function-field degree times its original divisor cycle. -/
theorem map_divisor_pullback_of_proper
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral X.left] [IsIntegral Y.left] (n : ℤ) (f : X ⟶ Y)
    [IsProper f.left] [IsDominant f.left]
    (hX : X.hom.relativeDimensionFunction δ (genericPoint X.left) = n)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (s : Y.left.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0) :
    map f.left (X.hom.relativeDimensionFunction δ)
        (Y.hom.relativeDimensionFunction δ)
        (@Scheme.nonzeroMeromorphicSectionDivisorCycle X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom) inferInstance
          ((Scheme.Modules.pullback f.left).obj ℒ) inferInstance
          (LocallyRingedSpace.Hom.pullbackMeromorphicSections f.left.toLRSHom
            (Scheme.Hom.MeromorphicFunction.pullbackDefined_of_isIntegral_of_isDominant f.left)
            ℒ s)
          (Scheme.Hom.MeromorphicFunction.pullbackSections_ne_zero_of_isDominant
            f.left ℒ s hs)) =
      (f.left.inducedFunctionFieldDegree : ℤ) •
        @Scheme.nonzeroMeromorphicSectionDivisorCycle Y.left
          (LocallyOfFiniteType.isLocallyNoetherian Y.hom) inferInstance
          ℒ inferInstance s hs := sorry

end AlgebraicGeometry.AlgebraicCycle
