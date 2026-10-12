/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap45.Lemma_45_14_7_Theory

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace WeilCohomology

/-- The product over the ground field of two smooth schemes is smooth. -/
instance schemeProduct_smooth
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Smooth X.hom] [Smooth Y.hom] : Smooth (X ⨯ Y).hom := sorry

/-- The product over the ground field of two projective schemes is projective. -/
instance schemeProduct_projective
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Projective X.hom] [Projective Y.hom] : Projective (X ⨯ Y).hom := sorry

/-- The product over the ground field of two nonempty schemes is nonempty. -/
instance schemeProduct_nonempty
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Nonempty X.left] [Nonempty Y.left] : Nonempty (X ⨯ Y).left := sorry

/-- The product over the ground field of two equidimensional smooth schemes is
equidimensional. -/
instance schemeProduct_equidimensional
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Smooth X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [EquidimensionalSpace Y.left] :
    EquidimensionalSpace (X ⨯ Y).left := sorry

end WeilCohomology
