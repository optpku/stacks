module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Saturation morphisms of groupoids in algebraic spaces

The saturation morphism associated to `g : U' ⟶ U` sends an arrow targeting
the image of an object of `U'` to its source.
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
  rfl

end AlgebraicGeometry.GroupoidAlgebraicSpace
