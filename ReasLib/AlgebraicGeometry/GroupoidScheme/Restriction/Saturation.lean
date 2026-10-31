/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The canonical saturation morphism is the second pullback projection followed by source. -/
def saturationMap {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) : Limits.pullback g G.t ⟶ G.U :=
  Limits.pullback.snd g G.t ≫ G.s

theorem saturationMap_def {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.U) :
    G.saturationMap g = Limits.pullback.snd g G.t ≫ G.s := rfl

end AlgebraicGeometry.GroupoidScheme
