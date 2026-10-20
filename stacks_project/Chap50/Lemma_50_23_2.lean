/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.Differential
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DeRham.Gysin

/- Lemma 50.23.2 -/
@[stacks 0G85] #check
  (@AlgebraicGeometry.Scheme.DeRham.Gysin.map_d :
    ∀ {X S : Scheme.{u}} (q : X ⟶ S) {c : ℕ}
      (fs : Fin c → Γ(X, ⊤)) (p : ℕ),
      restrictedMap q fs p ≫ targetDifferential q fs (p + c) =
        sourceDifferential q fs p ≫ restrictedMap q fs (p + 1) ≫
          eqToHom (congrArg (restrictedTarget q fs) (Nat.add_right_comm p 1 c)))

end AlgebraicGeometry.Scheme.DeRham.Gysin

end
