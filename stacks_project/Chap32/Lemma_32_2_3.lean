/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]
variable (c : Cone D) (hc : IsLimit c) (i₀ : I) {T : Scheme.{u}}
variable (t : T ⟶ D.obj (show OrderDual I from i₀))

/- Lemma 32.2.3: base changing a directed inverse limit of schemes over a fixed stage is the
limit of the base-changed inverse system over the stages above that stage. -/
@[stacks 01YZ] #check
  (AlgebraicGeometry.Scheme.isLimitBaseChangeOverCone D c hc
      (show OrderDual I from i₀) t :
    IsLimit (AlgebraicGeometry.Scheme.baseChangeOverCone D c
      (show OrderDual I from i₀) t))

end

end AlgebraicGeometry
