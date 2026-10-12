/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.Proper

universe u

variable {k : Type u} [Field k]
variable (X : AlgebraicGeometry.SchemeOverField k)

section

variable [AlgebraicGeometry.IsProper X.hom]

/- Lemma 33.27.2 (1): the normalization of a proper scheme over a field is proper over the same
field. -/
@[stacks 0GK4] #check
  (AlgebraicGeometry.SchemeOverField.Normalization.instIsProperNormalization X :
    AlgebraicGeometry.IsProper (AlgebraicGeometry.SchemeOverField.normalization X).hom)

end

section

variable [AlgebraicGeometry.Projective X.hom]

/- Lemma 33.27.2 (2): the normalization of a projective scheme over a field is projective over the
same field. -/
@[stacks 0GK4] #check
  (AlgebraicGeometry.SchemeOverField.Normalization.instProjectiveNormalization X :
    AlgebraicGeometry.Projective (AlgebraicGeometry.SchemeOverField.normalization X).hom)

end
