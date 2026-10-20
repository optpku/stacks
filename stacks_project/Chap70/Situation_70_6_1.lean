module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.MorphismBaseChange
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable (c : Cone D) (hc : IsLimit c)
variable (i0 i : I) (hi0i : i0 ≤ i)
variable [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
variable (X0 Y0 : AlgebraicSpace S) (x0 : X0 ⟶ D.obj i0) (y0 : Y0 ⟶ D.obj i0)
variable (f0 : X0 ⟶ Y0) (hf0 : f0 ≫ y0 = x0)
variable [IsQuasiCompact (D.obj i0)] [IsAbsolutelyQuasiSeparated (D.obj i0)]
variable [IsQuasiCompact X0] [IsAbsolutelyQuasiSeparated X0]
variable [IsQuasiCompact Y0] [IsAbsolutelyQuasiSeparated Y0]

/- Situation 70.6.1: let `S` be a scheme. Let `B = lim_i B_i` be the limit of a directed inverse
system of algebraic spaces over `S` with affine transition morphisms (Lemma 70.4.1). Fix a
distinguished stage `B₀ = D.obj i0`, a morphism `f0 : X0 ⟶ Y0` over `B₀` encoded by structure maps
`x0 : X0 ⟶ D.obj i0`, `y0 : Y0 ⟶ D.obj i0`, and a compatibility `hf0 : f0 ≫ y0 = x0`. Assume `B₀`,
`X0`, and `Y0` are quasi-compact and quasi-separated. For a stage `i` equipped with
`hi0i : i0 ≤ i`, the canonical stagewise base changes are represented by
`pullback y0 (D.map (homOfLE hi0i))`,
`pullback f0 (pullback.fst y0 (D.map (homOfLE hi0i)))`, and the induced morphism
`pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))`. The limit base change to
`B = c.pt` is represented by `pullback y0 (c.π.app i0)`, `pullback f0 (pullback.fst y0 (c.π.app i0))`,
and `pullback.snd f0 (pullback.fst y0 (c.π.app i0))`. -/
@[stacks 084W] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange.ofCone
    D i0 X0 Y0 c hc x0 y0 f0 hf0 :
    AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange D i0 X0 Y0)

#check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange.stageHom
    (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange.ofCone
      D i0 X0 Y0 c hc x0 y0 f0 hf0) i hi0i :
    pullback f0 (pullback.fst y0 (D.map (homOfLE hi0i))) ⟶
      pullback y0 (D.map (homOfLE hi0i)))

#check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange.limitHom
    (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange.ofCone
      D i0 X0 Y0 c hc x0 y0 f0 hf0) :
    pullback f0 (pullback.fst y0 (c.π.app i0)) ⟶ pullback y0 (c.π.app i0))

end
