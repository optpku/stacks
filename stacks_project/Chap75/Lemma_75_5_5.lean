module

public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_26_4_Pullback

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace CategoryTheory ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

namespace pullback

/-- Lemma 75.5.5: Let `S` be a scheme. Let `f : Y ⟶ X` be a morphism of algebraic
spaces over `S`. The functor `Lf^*` sends `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`. -/
@[stacks 08F4]
theorem mapsTo {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    derivedQuasiCoherentModuleProperty X ≤
      (derivedQuasiCoherentModuleProperty Y).inverseImage (modulePullbackDerived f) := sorry

end pullback

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
