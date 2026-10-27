/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Stalk
import StacksCheckRecall

/-!
# Relative flatness of quasi-coherent modules via étale stalks

A quasi-coherent module on an algebraic space is flat at a point over the target if and only if
its étale stalk at a geometric point over that point is flat along the induced map of étale
local rings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 67.31.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`. Let `F` be a quasi-coherent sheaf on `X`. Let `x ∈ |X|`. The following are
equivalent. (1) For some étale square `sq : EtaleSquare f`, with schemes `U`, `V` and étale
morphisms `a`, `b`, and some `u ∈ U` mapping to `x`, the restricted module
`(restrictFunctor sq.left.hom ⋙ restrictToScheme sq.left.left).obj F` is `Scheme.Modules.flatOverAt` over `V` at `u`.
(2) For any geometric point `xbar` lying over `x`, with `ybar = xbar.map f`, the étale stalk
`stalkModuleCat xbar F` is flat over `etaleLocalRing Y ybar` along
`etaleLocalRingMap f xbar`. -/
@[stacks 05VU] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverAt_iff_stalk_flatAlong :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent]
      (f : X ⟶ Y) (xbar : GeometricPoint X) (x : Points X) (hx : xbar.liesOver x),
    flatOverAt F f x ↔
      Module.FlatAlong (etaleLocalRingMap f xbar) (stalkModuleCat xbar F))

/- Relative flatness at the image of a geometric point is equivalent to flatness of the étale
stalk along the induced étale local ring map. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.flatOverAt_iff_stalk_flatAlong_image :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent]
      (f : X ⟶ Y) (xbar : GeometricPoint X),
    flatOverAt F f xbar.image ↔
      Module.FlatAlong (etaleLocalRingMap f xbar) (stalkModuleCat xbar F))

end AlgebraicGeometry.AlgebraicSpace.Modules

