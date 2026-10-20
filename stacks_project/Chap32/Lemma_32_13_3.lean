/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.AbsoluteNoetherianApproximation.Proper
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 32.13.3: let `f : X ⟶ S` be a proper morphism with `S` quasi-compact and
quasi-separated. Then `f` is the limit of an inverse system of proper morphisms
`X_i ⟶ S_i` with affine source and base transition morphisms and each `S_i` of finite type
over `ℤ`. -/
@[stacks 0A0P] #check
  (AlgebraicGeometry.Scheme.Limit.exists_properAbsoluteNoetherianApproximation :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.IsProper f]
      [CompactSpace S] [QuasiSeparatedSpace S],
      ∃ (I : Type u), ∃ (_ : Preorder I), ∃ (_ : Nonempty I),
        ∃ (_ : IsDirected I (· ≤ ·)), ∃ (Xsys : OrderDual I ⥤ AlgebraicGeometry.Scheme.{u}),
          ∃ (Ssys : OrderDual I ⥤ Over (AlgebraicGeometry.Spec
            (CommRingCat.of (ULift.{u} ℤ)))),
            ∃ (πX : (Functor.const (OrderDual I)).obj X ⟶ Xsys),
              ∃ (πS : (Functor.const (OrderDual I)).obj S ⟶
                Ssys ⋙ Over.forget (AlgebraicGeometry.Spec
                  (CommRingCat.of (ULift.{u} ℤ)))),
                ∃ (φ : Xsys ⟶ Ssys ⋙ Over.forget (AlgebraicGeometry.Spec
                  (CommRingCat.of (ULift.{u} ℤ)))),
                  AlgebraicGeometry.Scheme.Limit.IsProperAbsoluteNoetherianApproximation
                    f Xsys Ssys πX πS φ)
