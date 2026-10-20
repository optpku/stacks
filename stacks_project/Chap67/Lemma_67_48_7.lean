/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Normalization
import StacksCheckRecall

/-!
# Codimension-zero points of relative normalizations of schemes

A codimension-zero point of the relative normalization of a quasi-compact and
quasi-separated morphism of schemes is the image of a codimension-zero point of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.48.7: codimension-zero points of schemes are generic points of
irreducible components. Every such point of the relative normalization is the
image of a generic point of the source under the canonical factorization map. -/
@[stacks 0AYG] #check
  (AlgebraicGeometry.Scheme.Hom.surjOn_genericPoints_toNormalization :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f],
      Set.SurjOn f.toNormalization (genericPoints Y) (genericPoints f.normalization))
