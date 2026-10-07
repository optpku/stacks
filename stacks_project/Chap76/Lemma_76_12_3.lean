module

public import stacks_project.Chap76.Lemma_76_12_3_Comparison

/-!
# Conormal sheaves of first-order infinitesimal neighbourhoods

The canonical comparison from the conormal sheaf of an immersion of algebraic
spaces to the conormal sheaf of its first-order infinitesimal neighbourhood is
an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom.InfinitesimalNeighbourhood

/-- Lemma 76.12.3: Let `i : Z ⟶ X` be an immersion of algebraic spaces. Let
`Z ⊂ space i 1` be the first-order infinitesimal neighbourhood of `Z` in `X`.
The identity square relating `Z`, `space i 1`, and `X` induces, by
`Hom.Conormal.map`, a morphism
`Hom.conormalSheaf i ⟶ Hom.conormalSheaf (fromSource i 1)`, and this morphism
is an isomorphism. -/
@[stacks 05ZX, instance]
instance conormalComparison_isIso {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsImmersion i] :
    IsIso (conormalComparison i) :=
  sorry

end Hom.InfinitesimalNeighbourhood

end AlgebraicGeometry.AlgebraicSpace
