/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pushout.EtaleCube
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- 81.6.5.2: For a triple (V, U', φ) with U = U' ×_{X'} X and
G(V, U', φ) = V ⨿_U U', a chosen étale scheme presentation yields a commutative
cube with vertices U, U', V, G(V, U', φ) and scheme vertices U1, U1', V1,
G1(V1, U1', φ1). The side faces are cartesian, the front and back faces are
pushouts, and the northeast arrows — in particular G1 ⟶ G — are surjective
étale. In the shared cube, C.X1 = U1, C.X1' = U1', C.Y1' = G1, and
C.πY' is the map G1 → G. The additional pullback square specifies U1 = V1 ×_Y X. -/
@[stacks 07W2] #check
  (AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening.exists_cube_over :
    ∀ {S : Scheme.{u}} {X X' Y V U' G : AlgebraicSpace S}
      (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
      (pV : V ⟶ Y) (pU' : U' ⟶ X')
      (φ : Limits.pullback pV f ≅ Limits.pullback pU' i),
      φ.hom ≫ Limits.pullback.snd pU' i = Limits.pullback.snd pV f →
      ∀ (inlG : V ⟶ G) (inrG : U' ⟶ G),
        IsPushout (Limits.pullback.fst pU' i)
          (φ.inv ≫ Limits.pullback.fst pV f) inrG inlG →
        ∀ {V1 : Over S} (πV : ofOver V1 ⟶ V) [Etale πV] [Surjective πV],
          ∃ C : AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening.Cube
              (Limits.pullback.fst pU' i) (φ.inv ≫ Limits.pullback.fst pV f)
              inrG inlG πV,
            IsPullback (ofOverMap C.f1) (C.πX ≫ Limits.pullback.snd pU' i) (πV ≫ pV) f)
