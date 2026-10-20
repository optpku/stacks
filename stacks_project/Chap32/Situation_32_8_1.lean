/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.MorphismBaseChange
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable (i0 i : I) (hi0i : i0 ≤ i)
variable [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
variable (X0 Y0 : Scheme.{u}) (x0 : X0 ⟶ D.obj i0) (y0 : Y0 ⟶ D.obj i0) (f0 : X0 ⟶ Y0)
variable (hf0 : f0 ≫ y0 = x0)
variable [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
variable [CompactSpace X0] [QuasiSeparatedSpace X0]
variable [CompactSpace Y0] [QuasiSeparatedSpace Y0]

/- Situation 32.8.1: let `S = lim_i S_i` be the limit of a directed inverse system of schemes with
affine transition morphisms. Fix a distinguished stage `S₀ = D.obj i0`, a morphism
`f0 : X0 ⟶ Y0` over `S₀` encoded by structure maps `x0 : X0 ⟶ D.obj i0`,
`y0 : Y0 ⟶ D.obj i0`, and a compatibility `hf0 : f0 ≫ y0 = x0`. Assume `S₀`, `X0`, and `Y0` are
quasi-compact and quasi-separated. For a stage `i` equipped with `hi0i : i0 ≤ i`, the canonical
stagewise base changes are represented by
`pullback y0 (D.map (homOfLE hi0i)) : Scheme`,
`pullback f0 (pullback.fst y0 (D.map (homOfLE hi0i))) : Scheme`, and the induced morphism
`pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))`. The limit base change to
`S = c.pt` is represented by `pullback y0 (c.π.app i0)`, `pullback f0 (pullback.fst y0 (c.π.app i0))`,
and `pullback.snd f0 (pullback.fst y0 (c.π.app i0))`. -/
@[stacks 081D] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.ofCone
    D i0 X0 Y0 c hc x0 y0 f0 hf0 :
    AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange D i0 X0 Y0)

#check
  (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.stageHom
    (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.ofCone
      D i0 X0 Y0 c hc x0 y0 f0 hf0) i hi0i :
    pullback f0 (pullback.fst y0 (D.map (homOfLE hi0i))) ⟶
      pullback y0 (D.map (homOfLE hi0i)))

#check
  (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.limitHom
    (AlgebraicGeometry.Scheme.Limit.QcqsMorphismBaseChange.ofCone
      D i0 X0 Y0 c hc x0 y0 f0 hf0) :
    pullback f0 (pullback.fst y0 (c.π.app i0)) ⟶ pullback y0 (c.π.app i0))

end
