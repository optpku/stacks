/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RepresentablePushforward
import StacksCheckRecall

/-! # Representable pushforward of quasi-coherent modules -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces from `ofOver T` as a map of functors of points from
`yoneda.obj T`. -/
abbrev yonedaHomOf {S : Scheme.{u}} {T : Over S} {X : AlgebraicSpace S}
    (φ : ofOver T ⟶ X) : yoneda.obj T ⟶ X.functorOfPoints :=
  φ

end AlgebraicGeometry.AlgebraicSpace

/- 67.11.1.1: For a representable quasi-compact quasi-separated morphism and an étale surjective
scheme atlas, pushforward of a quasi-coherent module commutes with restriction to the atlas. -/
@[stacks 04CF] #check (AlgebraicGeometry.AlgebraicSpace.Modules.representablePushforwardIso :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    [QuasiCompact f] [QuasiSeparated f] {V : Over S} (g : ofOver V ⟶ Y)
    [Etale g] [Surjective g]
    (F : X.Modules) [F.IsQuasicoherent],
    (restrictFunctor g).obj ((pushforward f).obj F) ≅
      (pushforward (representablePullbackSnd hf g)).obj
        (restrict F (representablePullbackFst hf g)))

