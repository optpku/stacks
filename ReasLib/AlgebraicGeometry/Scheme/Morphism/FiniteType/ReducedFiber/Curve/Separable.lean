/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.ReducedFiber.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.ReducedFiber.Separable

/-!
# Separable normalized reduced fibres over regular curves

This module provides a finite separable function-field extension after which a normalized base
change is smooth at every generic point of every fibre over a regular integral curve.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom.smoothInCodimensionZero

/-- For a flat finite-type morphism to a one-dimensional regular integral Nagata scheme whose
generic-fibre component fields are separable over the function field, there is a finite separable
extension of the function field such that the normalization of the induced base change is smooth
at every generic point of every fibre. -/
theorem exists_separable_normalizedFunctionFieldExtension
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [FiniteType f]
    [Scheme.Nagata S] [IsIntegral S] [Scheme.Regular S]
    (hSdim : topologicalKrullDim S = 1)
    (h_generic_sep :
      let qK := Scheme.FunctionFieldExtension.map S S.functionField
      let X_K := pullback f qK
      ∀ η : X_K, η ∈ genericPoints X_K →
        ResidueField.IsSeparableOverSpec (pullback.snd f qK) η) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra S.functionField L)
        (_ : FiniteDimensional S.functionField L)
        (_ : Algebra.IsSeparable S.functionField L),
      let q := Scheme.FunctionFieldExtension.map S L
      let T := q.normalization
      let t : T ⟶ S := q.fromNormalization
      let X_T := pullback f t
      let Y := X_T.normalization
      let ν : Y ⟶ X_T := X_T.normalizationTo
      let g : Y ⟶ T := ν ≫ pullback.snd f t
      g.smoothInCodimensionZero := sorry

end AlgebraicGeometry.Scheme.Hom.smoothInCodimensionZero
