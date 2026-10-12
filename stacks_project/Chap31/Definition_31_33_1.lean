/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
import ReasLib.AlgebraicGeometry.Scheme.StrictTransform
import StacksCheckRecall

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {S S' X : Scheme.{u}}
variable (I : S.IdealSheafData) (b : S' ⟶ S) [IsBlowup b I]
variable (f : X ⟶ S) (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/- Definition 31.33.1 (1): the strict transform of a quasicoherent module is its pullback to
`X ×_S S'` modulo the sections supported on the inverse image of the exceptional divisor. -/
@[stacks 080D] #check
  (AlgebraicGeometry.strictTransformModule b (I.comap b) f ℱ :
    (AlgebraicGeometry.strictTransformAmbient b f).Modules)

/- Definition 31.33.1 (2): the strict transform of `X` is the closed subscheme of `X ×_S S'`
cut out by the ideal of sections supported on the inverse image of the exceptional divisor. -/
@[stacks 080D] #check
  (AlgebraicGeometry.strictTransform b (I.comap b) f : AlgebraicGeometry.Scheme.{u})

end

end AlgebraicGeometry
