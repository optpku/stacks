/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.Denominator
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

universe u

/- Lemma 31.23.9: A regular meromorphic section of an invertible module has a
quasi-coherent denominator ideal; its inclusion and multiplication map are
injective, and their cokernels have closed nowhere-dense support. -/
@[stacks 02P0] #check
  (AlgebraicGeometry.Scheme.regularMeromorphicSectionIdealSheaf :
    {X : AlgebraicGeometry.Scheme.{u}} →
      (ℒ : X.Modules) →
      [AlgebraicGeometry.Scheme.Modules.Invertible ℒ] →
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ) →
      X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s →
      AlgebraicGeometry.Scheme.RegularMeromorphicSectionIdealSheaf ℒ s)
