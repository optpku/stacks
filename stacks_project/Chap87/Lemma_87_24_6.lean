module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_24_6_Local

/-!
# Local character of morphisms locally of finite type

Lemma 87.24.6 records that a morphism of formal algebraic spaces is locally of
finite type if and only if this can be tested by a surjective étale square, by
every square with étale vertical arrows, or by Definition 87.11.1 coverings of
the target or of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
variable [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
variable (f : X ⟶ Y)

namespace LocallyOfFiniteType

/-- Lemma 87.24.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. The following are equivalent:
`LocallyOfFiniteType f`; `existsSurjectiveEtaleSquare f`, that there is a
commutative square of formal algebraic spaces with étale vertical arrows,
`U ⟶ X` surjective, and `U ⟶ V` locally of finite type;
`forallEtaleSquare f`, that every commutative square of formal algebraic
spaces with étale vertical arrows has locally-of-finite-type top arrow;
`existsCoverOnTarget f`, that some covering `{Y_ j ⟶ Y}` as in
Definition 87.11.1 has, for each `j`, a covering
`{X_ ji ⟶ Y_ j ×_Y X}` as in Definition 87.11.1 with each `X_ ji ⟶ Y_ j`
locally of finite type; and `existsCoverOnSource f`, that some covering
`{X_ i ⟶ X}` as in Definition 87.11.1 factors as `X_ i ⟶ Y_ i ⟶ Y` with
each `Y_ i` an affine formal algebraic space, each `Y_ i ⟶ Y` étale, and
each `X_ i ⟶ Y_ i` locally of finite type. -/
@[stacks 0ANL]
theorem tfae :
    List.TFAE [LocallyOfFiniteType f, existsSurjectiveEtaleSquare f,
      forallEtaleSquare f, existsCoverOnTarget f, existsCoverOnSource f] :=
  sorry

/-- Locally of finite type is equivalent to the existence of a commutative
square of formal algebraic spaces with étale vertical arrows, surjective
`U ⟶ X`, and locally-of-finite-type `U ⟶ V`. -/
theorem iff_existsSurjectiveEtaleSquare :
    LocallyOfFiniteType f ↔ existsSurjectiveEtaleSquare f :=
  sorry

/-- Locally of finite type is equivalent to the top arrow of every commutative
square of formal algebraic spaces with étale vertical arrows being locally of
finite type. -/
theorem iff_forallEtaleSquare :
    LocallyOfFiniteType f ↔ forallEtaleSquare f :=
  sorry

/-- Locally of finite type is equivalent to the existence of a
Definition 87.11.1 covering of `Y` and then of each `Y_ j ×_Y X` whose
projections `X_ ji ⟶ Y_ j` are locally of finite type. -/
theorem iff_existsCoverOnTarget :
    LocallyOfFiniteType f ↔ existsCoverOnTarget f :=
  sorry

/-- Locally of finite type is equivalent to the existence of a
Definition 87.11.1 covering of `X` factoring as `X_ i ⟶ Y_ i ⟶ Y` through
affine formal algebraic spaces with étale target legs and
locally-of-finite-type source legs. -/
theorem iff_existsCoverOnSource :
    LocallyOfFiniteType f ↔ existsCoverOnSource f :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.FormalAlgebraicSpace
