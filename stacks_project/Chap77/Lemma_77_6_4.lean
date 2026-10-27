/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Purity.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.6.4: A finite-type quasi-coherent module on a decent finite-type
morphism of algebraic spaces that is flat at every point over `y` and pure above
`y` is universally pure above `y`. -/
@[stacks 0CW4] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsPureAlong.universally_of_flatOverAt :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f] [Decent f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (y : Points Y),
      (∀ x ∈ Points.map f ⁻¹' {y}, flatOverAt ℱ f x) →
      ℱ.IsPureAlong f y → ℱ.IsUniversallyPureAlong f y)

end AlgebraicGeometry.AlgebraicSpace.Modules
