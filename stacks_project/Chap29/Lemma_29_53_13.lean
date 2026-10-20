/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Normalization.FiniteComponents

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.53.13: let `f : Y ⟶ X` be a quasi-compact and quasi-separated morphism. If `Y` is
normal and every quasi-compact open of `Y` has finitely many irreducible components, then the
normalization of `X` in `Y` is a disjoint union of normal integral schemes. -/
@[stacks 035L] #check
  (AlgebraicGeometry.Scheme.Hom.normalization_hasPairwiseDisjointOpenCoverByNormalIntegral_of_isNormal :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
      [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens Y] (_ : Y.isNormal),
      f.normalization.HasPairwiseDisjointOpenCoverByNormalIntegral)

#check
  (AlgebraicGeometry.Scheme.Hom.normalization_isNormal_of_isNormal :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
      [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens Y] (_ : Y.isNormal),
      f.normalization.isNormal)

#check
  (AlgebraicGeometry.Scheme.Hom.instIsDominantToNormalization :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f],
      IsDominant f.toNormalization)

#check
  (AlgebraicGeometry.Scheme.Hom.bijOn_genericPoints_toNormalization_of_isNormal :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
      [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens Y] (_ : Y.isNormal),
      Set.BijOn f.toNormalization (genericPoints Y) (genericPoints f.normalization))
