/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FppfEtale.Finite
import StacksCheckRecall

/-! # Finite fppf/étale derived comparison of algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FppfEtale
open CategoryTheory CategoryTheory.GrothendieckTopology

universe u

/- Lemma 84.6.6: for a finite morphism of algebraic spaces, the canonical
base-change map identifies `a_Y⁻¹(R f_small,* K)` with
`R f_big,fppf,* (a_X⁻¹ K)` for every `K` in `D⁺(X_étale)`. -/
@[stacks 0DGK] #check (AlgebraicGeometry.AlgebraicSpace.FppfEtale.finite_derivedPushforward :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})),
    IsIso (derivedBaseChangeApp f K))

end
