/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]

/- Definition 29.5.5: the canonical datum cuts out the closed subscheme constructed in
Lemma 29.5.4. -/
@[stacks 05JV] #check (AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport ℱ : X.IdealSheafData)

end AlgebraicGeometry.Scheme.Modules
