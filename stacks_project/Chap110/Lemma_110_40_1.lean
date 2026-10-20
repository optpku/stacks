/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.Counterexample

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 110.40.1: there exist affine schemes `X`, `S`, a morphism `f : X ⟶ S` of
finite presentation, and a finitely presented `𝒪_X`-module `ℱ` that is pure relative
to `S` but not universally pure relative to `S`. -/
@[stacks 05JK]
#check (AlgebraicGeometry.Scheme.Modules.exists_isPureOver_not_isUniversallyPureOver :
    ∃ (X S : Scheme.{u}) (_ : IsAffine X) (_ : IsAffine S) (f : X ⟶ S)
      (_ : Scheme.Hom.FinitePresentation f) (ℱ : X.Modules)
      (_ : ℱ.IsFinitePresentation),
      ℱ.IsPureOver f ∧ ¬ ℱ.IsUniversallyPureOver f)

end AlgebraicGeometry.Scheme.Modules
