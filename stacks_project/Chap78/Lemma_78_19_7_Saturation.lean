/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Saturation

/-!
# Saturation morphisms of restricted groupoids in algebraic spaces

The saturation morphism of a restriction along `g : U' ⟶ U` is the composite
`h = s ∘ pr₁ : U' ×_{g, U, t} R ⟶ U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.saturationMap :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U),
    Limits.pullback g G.t ⟶ G.U)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.saturationMap_def :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U),
    G.saturationMap g = Limits.pullback.snd g G.t ≫ G.s)

end AlgebraicGeometry.GroupoidAlgebraicSpace
