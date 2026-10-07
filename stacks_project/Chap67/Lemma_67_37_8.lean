module

public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Lemma_67_36_4_Syntomic

/-!
# Smooth morphisms of algebraic spaces are syntomic
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Smooth

/-- Lemma 67.37.8: A smooth morphism of algebraic spaces is syntomic. -/
@[stacks 06CP]
instance syntomic {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Smooth f] : Syntomic f :=
  sorry

end Smooth

end AlgebraicGeometry.AlgebraicSpace
