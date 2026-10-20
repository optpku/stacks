/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Affine
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.4.13: in Situation `32.4.5`, if the limit scheme is affine, then after
passing to some stage `i₀`, every later stage is affine. -/
@[stacks 01Z6] #check
  (AlgebraicGeometry.Scheme.Limit.exists_eventually_isAffine_of_isLimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, CompactSpace (D.obj j)]
      [∀ j, QuasiSeparatedSpace (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      [IsAffine c.pt],
      ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsAffine (D.obj i))
