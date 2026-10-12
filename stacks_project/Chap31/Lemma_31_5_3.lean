/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Support
import StacksCheckRecall

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules)
variable [ℱ.IsQuasicoherent]

/- Lemma 31.5.3: For a quasi-coherent `𝒪_X`-module `ℱ` on a scheme `X`,
`associatedPoints ℱ ⊆ ℱ.weakAss ⊆ moduleSupport ℱ`. -/
@[stacks 05AM] #check
  (AlgebraicGeometry.Scheme.Modules.associatedPoints_subset_weakAss ℱ :
    associatedPoints ℱ ⊆ ℱ.weakAss)

#check
  (AlgebraicGeometry.Scheme.Modules.weakAss_subset_support ℱ :
    ℱ.weakAss ⊆ moduleSupport ℱ)

end AlgebraicGeometry.Scheme.Modules
