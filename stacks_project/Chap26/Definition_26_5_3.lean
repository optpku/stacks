/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Definition 26.5.3: the affine structure sheaf, affine spectrum, and the
associated tilde module use their canonical mathlib owners. -/
section

variable (R : CommRingCat)

@[stacks 01HU] #check Spec.structureSheaf
@[stacks 01HU] #check (Spec R).toLocallyRingedSpace

end

@[stacks 01HU "affine spectrum"] #check Spec
#check Scheme.forgetToLocallyRingedSpace
@[stacks 01HU] #check tilde
#check tilde.functor
