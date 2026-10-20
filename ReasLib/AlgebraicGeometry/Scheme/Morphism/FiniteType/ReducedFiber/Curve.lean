/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.ReducedFiber.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Normalized reduced fibres over regular curves

This module provides a finite function-field extension after which a normalized base change is
smooth at every generic point of every fibre over a regular integral curve.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a flat finite-type morphism to a one-dimensional regular integral Nagata scheme, there
is a finite extension of the function field such that the normalization of the induced base
change is smooth at every generic point of every fibre. -/
@[stacks 0BRQ]
theorem exists_normalizedFunctionFieldExtension_smoothInCodimensionZero
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [FiniteType f]
    [Scheme.Nagata S] [IsIntegral S] [Scheme.Regular S]
    (hSdim : topologicalKrullDim S = 1) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra S.functionField L)
        (_ : FiniteDimensional S.functionField L),
      let q := Scheme.FunctionFieldExtension.map S L
      let T := q.normalization
      let t : T ⟶ S := q.fromNormalization
      let X_T := pullback f t
      let Y := X_T.normalization
      let ν : Y ⟶ X_T := X_T.normalizationTo
      let g : Y ⟶ T := ν ≫ pullback.snd f t
      g.smoothInCodimensionZero := sorry

end AlgebraicGeometry.Scheme.Hom
