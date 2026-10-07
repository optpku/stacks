module

public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Definition_67_5_2_Surjective

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flat

/-- Lemma 74.9.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. If `f` is flat and surjective and `X` is reduced, then `Y` is
reduced. -/
@[stacks 06MI]
theorem isReduced_of_surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Flat f] [Surjective f] [IsReduced X] : IsReduced Y := sorry

end AlgebraicGeometry.AlgebraicSpace.Flat
