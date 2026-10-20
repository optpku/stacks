module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.InfinitesimalNeighbourhood
import StacksCheckRecall

/-!
# Conormal sheaves of first-order infinitesimal neighbourhoods

The canonical comparison from the conormal sheaf of an immersion of algebraic
spaces to the conormal sheaf of its first-order infinitesimal neighbourhood is
an isomorphism.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.12.3: Let `i : Z ⟶ X` be an immersion of algebraic spaces. Let
`Z ⊂ space i 1` be the first-order infinitesimal neighbourhood of `Z` in `X`.
The identity square relating `Z`, `space i 1`, and `X` induces, by
`Hom.Conormal.map`, a morphism
`Hom.conormalSheaf i ⟶ Hom.conormalSheaf (fromSource i 1)`, and this morphism
is an isomorphism. -/
@[stacks 05ZX]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood.conormalComparison_isIso :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i],
    IsIso (AlgebraicGeometry.AlgebraicSpace.Hom.InfinitesimalNeighbourhood.conormalComparison i))

