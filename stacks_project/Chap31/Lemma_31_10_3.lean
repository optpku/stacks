/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.FittingIdeal

open AlgebraicGeometry
open scoped AlgebraicGeometry RelativeDerivation

universe u

/- Lemma 31.10.3: for a flat, locally finitely presented morphism whose nonempty fibres are
equidimensional of dimension `d`, the support of the `d`th Fitting ideal sheaf of relative
differentials is exactly the nonsmooth locus. -/
@[stacks 0C3K] #check
  (AlgebraicGeometry.Scheme.Hom.fittingIdealSheaf_differentials_support_eq_compl_smoothLocus :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) [Flat f] [LocallyOfFinitePresentation f]
      [Scheme.Hom.RelativeDimension f d],
      ((Scheme.fittingIdealSheaf (Ω[f.toShHom]) d).support : Set X) =
        (f.smoothLocus : Set X)ᶜ)
