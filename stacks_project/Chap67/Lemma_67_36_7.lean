module

public import stacks_project.Chap67.Lemma_67_36_4_Syntomic
public import stacks_project.Chap67.Lemma_67_6_3_UniversallyOpen

/-!
# Syntomic morphisms of algebraic spaces are universally open
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.36.7: A syntomic morphism is universally open. -/
@[stacks 0DF0]
instance UniversallyOpen.of_syntomic {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Syntomic f] : UniversallyOpen f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
