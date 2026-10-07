module

public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty

/-!
# Smooth surjective algebraic-space atlases imply algebraic stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 94.15.3: let `S` be a scheme contained in `Sch_fppf`. Let
`u : U ⟶ X` be a 1-morphism of stacks in groupoids over `(Sch/S)_fppf`,
i.e. `[IsStack.InGroupoids (Scheme.fppfTopology.over S) U.p]` and
`[IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]`. If `U` is
representable by an algebraic space (`hU : IsRepresentableByAlgebraicSpace U`)
and `u` is representable by algebraic spaces, surjective and smooth
(`[Groupoids.Hom.Smooth u]` and `[Groupoids.Hom.Surjective u]`), then `X` is
an algebraic stack over `S`. -/
@[stacks 05UL]
theorem of_smooth_surjective {S : Scheme.{u}} {U X : GroupoidsOver S}
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) U.p]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) X.p]
    (u : U ⟶ X) (hU : IsRepresentableByAlgebraicSpace U)
    [Groupoids.Hom.Smooth u] [Groupoids.Hom.Surjective u] :
    AlgebraicStack X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
