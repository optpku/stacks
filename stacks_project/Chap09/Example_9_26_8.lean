/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Geometry.Manifold.Complex.FunctionField
import StacksCheckRecall

@[expose] public section

open scoped IntermediateField Manifold MeromorphicFunctionField

universe u

variable (X Y : CompactRiemannSurface.{u})

/- Example 9.26.8 (Tag 09IB): the meromorphic function field of a compact Riemann surface has
transcendence degree one over `ℂ`; conversely, every essentially finite type extension of `ℂ` of
transcendence degree one is realized by such a surface. Meromorphic pullback gives an
anti-equivalence between nonconstant holomorphic maps and complex-algebra maps of these fields. -/

@[stacks 09IB]
#check (CompactRiemannSurface.functionField_trdeg_eq_one X : Algebra.trdeg ℂ (ℂ(X)) = 1)
#check CompactRiemannSurface.existsWithFunctionFieldOfEssFiniteTypeTrdegEqOne
#check (CompactRiemannSurface.nonemptyIsoIffNonemptyFunctionFieldAlgEquiv X Y :
  Nonempty (X ≅ Y) ↔ Nonempty (ℂ(Y) ≃ₐ[ℂ] ℂ(X)))
#check (inferInstance : Algebra.EssFiniteType ℂ (ℂ(X)))
#check MeromorphicFunctionField.pullback
#check CompactRiemannSurface.functionFieldFunctor
#check (inferInstance : CompactRiemannSurface.functionFieldFunctor.{u}.Full)
#check (inferInstance : CompactRiemannSurface.functionFieldFunctor.{u}.Faithful)
#check (inferInstance : CompactRiemannSurface.functionFieldFunctor.{u}.EssSurj)
@[stacks 09IB]
#check (inferInstance : CompactRiemannSurface.functionFieldFunctor.{u}.IsEquivalence)
