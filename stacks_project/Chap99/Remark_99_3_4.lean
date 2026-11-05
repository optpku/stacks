/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomFunctor.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Remark 99.3.4: in Situation 99.3.1, for a morphism `φ : B' ⟶ B` of algebraic
spaces over `S`, set `X' = X ×_B B'` and write `F'`, `G'` for the pullbacks of
`F`, `G` to `X'`. The Hom functor of `(f' : X' ⟶ B', F', G')` on schemes over
`B'` satisfies `Hom(F', G')(T) ≃ Hom(F, G)(T)` when a scheme `T` over `B'` is
viewed as a scheme over `B` via `T ⟶ B' ⟶ B`. -/
@[stacks 08JW] #check ((fun {S} {X B B'} f φ F G _ _ σ => AlgebraicGeometry.AlgebraicSpace.Modules.homFunctorBaseChangeEquiv f φ F G σ) :
  ∀ {S : Scheme.{u}} {X B B' : AlgebraicSpace S} (f : X ⟶ B) (φ : B' ⟶ B)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (σ : SchemeOver B'),
    (homFunctor (pullback.snd f φ) ((pullback (pullback.fst f φ)).obj F)
        ((pullback (pullback.fst f φ)).obj G)).obj (op σ) ≃
      (homFunctor f F G).obj (op ((CostructuredArrow.map φ).obj σ)))

#check ((fun {S} {X B B'} f φ F G _ _ => AlgebraicGeometry.AlgebraicSpace.Modules.homFunctor_baseChange f φ F G) :
  ∀ {S : Scheme.{u}} {X B B' : AlgebraicSpace S} (f : X ⟶ B) (φ : B' ⟶ B)
    (F G : X.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent],
    homFunctor (pullback.snd f φ) ((pullback (pullback.fst f φ)).obj F)
        ((pullback (pullback.fst f φ)).obj G) ≅
      (CostructuredArrow.map φ).op ⋙ homFunctor f F G)

end AlgebraicGeometry.AlgebraicSpace.Modules
