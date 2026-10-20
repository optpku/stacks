/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.TwoMorphism
import StacksCheckRecall

/-!
# Recovering morphisms of algebraic spaces from small étale ringed topoi

A `2`-endomorphism of the small étale ringed-topos morphism induced by a morphism of algebraic
spaces is the identity `2`-morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
universe u

/- Lemma 66.28.2: let `S` be a scheme. Let `X`, `Y` be algebraic spaces over `S`. Let
`f : X ⟶ Y` be a morphism of algebraic spaces over `S`. Every `2`-morphism from
`(f_small, f^♯)` to itself, in the sense of `RingedSite.ToposHom.TwoMorphism`
(Modules on Sites, Definition 18.8.1), equals the identity `2`-morphism. Here
`(f_small, f^♯)` is `ringedToposHom f`, with `f_small = (ringedToposHom f).toTopos` and
`f^♯ = (ringedToposHom f).structureMap`. -/
@[stacks 04KK]
#check (AlgebraicGeometry.AlgebraicSpace.smallEtaleRingedTopos_twoMorphism_eq_id :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (t : RingedSite.ToposHom.TwoMorphism.{u + 1, u, u + 1, u, u}
      (ringedToposHom f) (ringedToposHom f)),
    t = RingedSite.ToposHom.TwoMorphism.refl.{u + 1, u, u + 1, u, u} (ringedToposHom f))
