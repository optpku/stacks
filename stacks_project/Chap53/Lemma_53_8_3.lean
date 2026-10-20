/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.RiemannRoch
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.DerivedQCoh
open ProperDualizingComplex

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.8.3: for a proper one-dimensional Gorenstein scheme `X` over `k` whose
global functions are `k`, the degree of the curve dualizing module is `2g - 2`. -/
@[stacks 0C19] #check (AlgebraicGeometry.SchemeOverField.curveDualizingModuleDegree_eq_genus :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      [Scheme.Gorenstein X.left]
      (h_dimension : topologicalKrullDim X.left = 1)
      (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
    -- Local instance justification (defeq pin): the dependent degree expression requires the
    -- invertibility instance using equidimensionality derived from the explicit dimension
    -- and global-functions hypotheses, without adding an independent assumption.
    let _ : EquidimensionalSpace X.left :=
      equidimensionalSpace_of_dim_one_of_globalSectionsMap_bijective X h_dimension hΓ
    -- Local instance justification (defeq pin): the dependent degree expression requires the
    -- invertibility instance using the canonical Fact wrapper of the explicit dimension equality.
    let _ : Fact (topologicalKrullDim X.left = 1) := ⟨h_dimension⟩
    Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le
        (curveDualizingModule X.hom) =
      2 * (genus X h_dimension hΓ : ℤ) - 2)

end AlgebraicGeometry.SchemeOverField
