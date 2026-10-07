module

public import stacks_project.Chap03.Lemma_3_9_4_Size

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Cardinal AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Size of schemes is invariant under isomorphism. -/
theorem size_eq_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) : X.size = Y.size := sorry

/-- An open immersion identifies the size of the source with the size of its open image. -/
theorem size_opensRange {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] :
    Y.size = f.opensRange.toScheme.size := sorry

end AlgebraicGeometry.Scheme
