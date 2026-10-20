/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.QCartier
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Scheme

/- Exercise 111.49.6: there exists a Weil divisor `D` on a variety which is not
the Weil divisor associated to any Cartier divisor, yet `n • D` is the Weil
divisor associated to a Cartier divisor for some integer `n > 1`. -/
@[stacks 02F9] #check (AlgebraicGeometry.exists_weilDivisor_nsmul_ofCartier_not_ofCartier :
    ∃ (k : Type u) (_ : Field k) (X : SchemeOverField k) (_ : Variety X)
      (_ : IsNoetherian X.left)
      (_ : HasSheafify (Opens.grothendieckTopology X.left.toTopCat) AddCommGrpCat.{u})
      (_ : (Opens.grothendieckTopology X.left.toTopCat).HasSheafCompose
        (forget CommRingCat.{u}))
      (D : WeilDivisor X.left) (n : ℕ),
      1 < n ∧
        (∀ τ : CartierDivisor X.left, weilDivisor_ofCartier τ ≠ D) ∧
          ∃ τ : CartierDivisor X.left, weilDivisor_ofCartier τ = n • D)

end AlgebraicGeometry
