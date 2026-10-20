/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Affine

open CategoryTheory TopCat TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Conormal

section

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
variable (U : X.Opens) (j : Z ⟶ U) [IsClosedImmersion j]
variable (h : j ≫ U.ι = i)

/- Lemma 29.31.2: for a closed factorization of an immersion through an open subscheme, the
conormal sheaf is canonically compared with the pullback of the kernel ideal sheaf. -/
@[stacks 01R3] #check
  (AlgebraicGeometry.Scheme.Hom.Conormal.factorizationPullbackComparisons i j U.ι h :
    IsIso (AlgebraicGeometry.Scheme.Hom.Conormal.factorizationConormalComparison
      i j U.ι h) ∧
      IsIso (AlgebraicGeometry.Scheme.Hom.Conormal.pullbackIdealComparison j))

/- The pushed-forward conormal sheaf is canonically compared with the ambient kernel-cotangent
sheaf `I / I²`. -/
#check
  (AlgebraicGeometry.Scheme.Hom.Conormal.factorizationPushforwardComparisons i j U.ι h :
    IsIso ((Scheme.Modules.pushforward j).map
      (AlgebraicGeometry.Scheme.Hom.Conormal.factorizationConormalComparison
        i j U.ι h)) ∧
      IsIso (AlgebraicGeometry.Scheme.Hom.Conormal.pushforwardConormalComparison j))

end


section

variable {R : Type u} [CommRing R] (I : Ideal R)

/- On the affine quotient chart, the canonical map from `I / I²` to conormal global sections is
invertible. -/
#check
  (AlgebraicGeometry.Scheme.Hom.Conormal.quotientMapCotangentToSections_isIso I :
    IsIso (AlgebraicGeometry.Scheme.Hom.Conormal.quotientMapCotangentToSections I))

end


end AlgebraicGeometry.Scheme.Hom.Conormal
