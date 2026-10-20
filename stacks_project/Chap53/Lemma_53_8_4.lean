/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Differentials
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.8.4 (1): for a smooth proper one-dimensional scheme over a field with
bijective global-sections map, the finrank of global relative differentials is the genus. -/
@[stacks 0C1A] #check (AlgebraicGeometry.SchemeOverField.differentialFinrank_eq_genus :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
    Scheme.Hom.cohomologyFinrank X.hom (Ω[X.hom.toShHom]) 0 =
      genus X h_dimension hΓ)

/- Lemma 53.8.4 (2): under the same hypotheses, the curve degree of the rank-one
relative differential module is `2 * (genus X h_dimension hΓ : ℤ) - 2`. -/
@[stacks 0C1A] #check (AlgebraicGeometry.SchemeOverField.differentialDegree_eq_genus :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [SmoothOfRelativeDimension 1 X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
    Scheme.Modules.curveDegree X.hom h_dimension.le (Ω[X.hom.toShHom]) 1 =
      2 * (genus X h_dimension hΓ : ℤ) - 2)

end AlgebraicGeometry.SchemeOverField
