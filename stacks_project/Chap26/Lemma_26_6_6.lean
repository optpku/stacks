module

public import Mathlib.AlgebraicGeometry.AffineScheme
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (Y : Scheme.{u}) [IsAffine Y] (f : Γ(Y, ⊤))

/- Lemma 26.6.6: a principal open in an affine scheme is affine. -/
@[stacks 01I3] #check IsAffineOpen.basicOpen (isAffineOpen_top Y) f

/- General companion: a principal open inside any affine open is affine. -/
#check IsAffineOpen.basicOpen

end AlgebraicGeometry.Scheme
