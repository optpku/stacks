/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.AbsoluteNoetherianApproximation
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Proposition 32.5.4: every quasi-compact and quasi-separated scheme is an inverse limit of
schemes of finite type over `ℤ` with affine transition morphisms. -/
@[stacks 01ZA] #check
  (AlgebraicGeometry.exists_absoluteNoetherianApproximation :
    ∀ (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S],
      ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (D : OrderDual I ⥤ Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
        (cS : Cone (D ⋙ Over.forget (Spec (CommRingCat.of (ULift.{u} ℤ)))))
        (hcS : IsLimit cS) (eS : S ≅ cS.pt)
        (h_affine : ∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii')).left),
          ∀ i : I, Scheme.Hom.FiniteType (D.obj i).hom)
