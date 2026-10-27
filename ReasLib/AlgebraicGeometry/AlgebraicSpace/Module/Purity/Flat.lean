/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Purity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.IsPureAlong

/-- For a decent finite-type morphism of algebraic spaces over a scheme, a finite-type
quasi-coherent module that is flat at every point over `y` and pure above `y` is
universally pure above `y`. -/
@[stacks 0CW4]
theorem universally_of_flatOverAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [Decent f] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (y : Points Y)
    (h_flat : ∀ x ∈ Points.map f ⁻¹' {y}, flatOverAt ℱ f x)
    (h_pure : ℱ.IsPureAlong f y) :
    ℱ.IsUniversallyPureAlong f y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.IsPureAlong

namespace AlgebraicGeometry.AlgebraicSpace.Modules.IsPureOver

/-- For a decent finite-type morphism of algebraic spaces over a scheme, a finite-type
quasi-coherent module that is flat over the target is pure relative to the target
if and only if it is universally pure relative to the target. -/
@[stacks 0CW5]
theorem iff_universally_of_flatOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] [Decent f] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (h_flat : ∀ x : Points X, flatOverAt ℱ f x) :
    ℱ.IsPureOver f ↔ ℱ.IsUniversallyPureOver f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.IsPureOver
