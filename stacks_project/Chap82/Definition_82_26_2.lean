module

import StacksCheckRecall
public import stacks_project.Chap82.Definition_82_26_2_ChowCohomology

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 82.26.2: In Situation 82.2.1, for good `X / B`, the Chow
cohomology of `X` is the graded `ℤ`-algebra `ring δ f` whose degree-`p`
component is `degree δ f p`, i.e. `A^p(X ⟶ X)`, the bivariant classes of
`𝟙 X` on Chow groups. No commutativity is asserted. -/
@[stacks 0ERK] #check (AlgebraicGeometry.AlgebraicSpace.ChowCohomology.ring :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f],
    Type (u + 1))
