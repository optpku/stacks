/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Spec
import Mathlib.CategoryTheory.Category.Preorder
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.Noetherian
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c)
variable (i i' : I) (hii' : i ≤ i')
variable [∀ j, IsNoetherian (D.obj j)]
variable [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]

/- Situation 70.23.1: let `S` be a scheme, for example `Spec ℤ`. Let `B = lim_i B_i` be
the limit of a directed inverse system of Noetherian algebraic spaces over `S` with affine
transition morphisms `B_{i'} ⟶ B_i` for `i ≤ i'`. -/
@[stacks 0CP6] #check
  (AlgebraicGeometry.AlgebraicSpace.IsNoetherianAffineLimitSystem :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S : Scheme.{u}}
      (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c), Prop)

#check (hc : CategoryTheory.Limits.IsLimit c)
#check (c.pt : AlgebraicSpace S)
#check (c.π.app i : c.pt ⟶ D.obj i)
#check (inferInstance : IsNoetherian (D.obj i))
#check (D.map (homOfLE hii') : D.obj i' ⟶ D.obj i)
#check (inferInstance : Affine (D.map (homOfLE hii')))
#check (Spec (CommRingCat.of (ULift.{u} ℤ)) : Scheme.{u})

end
