module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ProjectiveSpace.FermatCurve

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace.FermatCurve
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.FermatCurve

/- Exercise 111.63.5 (1): Let `k` be an algebraically closed field of characteristic `0`. Let
`X : T_0 ^ d + T_1 ^ d - T_2 ^ d = 0 ⊂ P^2_k` be the Fermat curve of degree `d ≥ 3`. Let
`p = [1 : 0 : 1]` and `q = [0 : 1 : 1]` on `X`, and set `D = [p] - [q]`. Then `D` is nontrivial
in the Weil divisor class group. -/
@[stacks 0G17]
#check (AlgebraicGeometry.ProjectiveSpace.FermatCurve.divisorClass_ne_zero :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (d : ℕ) (hd : 3 ≤ d) [NeZero d]
    [Curve (over k d)] [IsIntegral (scheme k d)] [IsLocallyNoetherian (scheme k d)],
    weilDivisorClassGroupMk (scheme k d) (divisor k d) ≠ 0)

/- Exercise 111.63.5 (2): Let `k` be an algebraically closed field of characteristic `0`. Let
`X : T_0 ^ d + T_1 ^ d - T_2 ^ d = 0 ⊂ P^2_k` be the Fermat curve of degree `d ≥ 3`. Let
`p = [1 : 0 : 1]` and `q = [0 : 1 : 1]` on `X`, and set `D = [p] - [q]`. Then `d D` is trivial
in the Weil divisor class group. -/
@[stacks 0G17]
#check (AlgebraicGeometry.ProjectiveSpace.FermatCurve.nsmul_divisorClass_eq_zero :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (d : ℕ) (hd : 3 ≤ d) [NeZero d]
    [Curve (over k d)] [IsIntegral (scheme k d)] [IsLocallyNoetherian (scheme k d)],
    weilDivisorClassGroupMk (scheme k d) (d • divisor k d) = 0)

/- The multiple `d D` is a principal Weil divisor on the Fermat curve. -/
#check (AlgebraicGeometry.ProjectiveSpace.FermatCurve.nsmul_divisor_isPrincipal :
  ∀ {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (d : ℕ) (hd : 3 ≤ d) [NeZero d]
    [Curve (over k d)] [IsIntegral (scheme k d)] [IsLocallyNoetherian (scheme k d)],
    IsPrincipalWeilDivisor (scheme k d) (d • divisor k d))

end AlgebraicGeometry.ProjectiveSpace.FermatCurve
