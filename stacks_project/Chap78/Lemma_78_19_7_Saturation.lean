/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import stacks_project.Chap78.Definition_78_11_1_Groupoid

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

/-- The saturation morphism `h = s ∘ pr₁` of a restriction along `g : U' ⟶ U`,
sending a pair consisting of an object over `U'` and an arrow targeting its image
to the source of that arrow. -/
def saturationMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    Limits.pullback g G.t ⟶ G.U :=
  Limits.pullback.snd g G.t ≫ G.s

/-- The saturation morphism is the source map after the second pullback projection. -/
theorem saturationMap_def {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {U' : Over B} (g : U' ⟶ G.U) :
    G.saturationMap g = Limits.pullback.snd g G.t ≫ G.s :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
