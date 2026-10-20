/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Normalization
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.53.12: let `f : Y ⟶ X` be an integral morphism. Then the normalization of `X`
in `Y` is equal to `Y`; equivalently, the canonical morphism to the relative normalization is an
isomorphism. -/
@[stacks 03GP] #check
  (AlgebraicGeometry.Scheme.Hom.instIsIsoToNormalizationOfIsIntegralHom :
    ∀ {Y X : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      [AlgebraicGeometry.IsIntegralHom f],
      CategoryTheory.IsIso f.toNormalization)
