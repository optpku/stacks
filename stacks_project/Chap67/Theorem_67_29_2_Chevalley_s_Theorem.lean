/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Constructible.Image
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Theorem 67.29.2 (Chevalley's Theorem): let `S` be a scheme, and let `f : X ⟶ Y` be a
quasi-compact morphism of algebraic spaces over `S` which is locally of finite presentation.
Then the image of every étale locally constructible subset of `|X|` is an étale locally
constructible subset of `|Y|`. -/
@[stacks 0ECX] #check (AlgebraicGeometry.AlgebraicSpace.IsEtaleLocallyConstructible.image :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [LocallyOfFinitePresentation f] {E : Set (Points X)},
    IsEtaleLocallyConstructible E → IsEtaleLocallyConstructible (Points.map f '' E))

end AlgebraicGeometry.AlgebraicSpace
