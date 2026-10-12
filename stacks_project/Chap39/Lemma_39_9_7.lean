/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.MulBy

@[expose] public section

open CategoryTheory MonoidalCategory
open scoped AbelianVariety CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.AbelianVariety

/- Lemma 39.9.7: Pullback of an invertible module on an abelian variety along multiplication by
`n` is isomorphic to the tensor product of the indicated powers of the module and its pullback
along inversion. -/
@[stacks 0BFF] #check (AlgebraicGeometry.AbelianVariety.mulByPullbackIso :
  ∀ {k : Type u} [Field k] (A : SchemeOverField k) [GrpObj A] [AbelianVariety A]
    (L : A.left.Modules) [Scheme.Modules.Invertible L] (n : ℕ),
    Nonempty
      ((Scheme.Modules.pullback ([n]ₐ A)).obj L ≅
        RingedSpace.TensorPower.sheaf L (n * (n + 1) / 2) ⊗
          RingedSpace.TensorPower.sheaf
            ((Scheme.Modules.pullback (ι[A].left)).obj L) (n * (n - 1) / 2)))

end AlgebraicGeometry.AbelianVariety
