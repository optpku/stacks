module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_19_4_Local

/-!
# Local character of representability by algebraic spaces

Lemma 87.19.4 records that a morphism of formal algebraic spaces is
representable by algebraic spaces if and only if this can be tested by a
surjective étale square, by every square with representable vertical arrows,
or by Definition 87.11.1 coverings of the target or of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits ChosenBigFppfSite

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
variable (f : X ⟶ Y)

namespace representableByAlgebraicSpaces

/-- Lemma 87.19.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. The following are equivalent:
`representableByAlgebraicSpaces f`; `existsSurjectiveEtaleSquare f`, that
there is a commutative square of formal algebraic spaces with representable
vertical arrows, `U ⟶ X` surjective étale, and `U ⟶ V` representable;
`forallVerticalRepresentable f`, that every commutative square of formal
algebraic spaces with representable vertical arrows has representable top
arrow; `existsCoverOnTarget f`, that some covering `{Y_ j ⟶ Y}` as in
Definition 87.11.1 has, for each `j`, a covering
`{X_ ji ⟶ Y_ j ×_Y X}` as in Definition 87.11.1 with each `X_ ji ⟶ Y_ j`
representable by algebraic spaces; and `existsCoverOnSource f`, that some
covering `{X_ i ⟶ X}` as in Definition 87.11.1 factors as
`X_ i ⟶ Y_ i ⟶ Y` with each `Y_ i` an affine formal algebraic space and both
legs representable by algebraic spaces. -/
@[stacks 0AN4]
theorem tfae :
    List.TFAE [representableByAlgebraicSpaces f, existsSurjectiveEtaleSquare f,
      forallVerticalRepresentable f, existsCoverOnTarget f,
      existsCoverOnSource f] :=
  sorry

/-- Representability by algebraic spaces is equivalent to the existence of a
commutative square of formal algebraic spaces with representable vertical
arrows, surjective étale `U ⟶ X`, and representable `U ⟶ V`. -/
theorem iff_existsSurjectiveEtaleSquare :
    representableByAlgebraicSpaces f ↔ existsSurjectiveEtaleSquare f :=
  sorry

/-- Representability by algebraic spaces is equivalent to representability of
the top arrow of every commutative square of formal algebraic spaces with
representable vertical arrows. -/
theorem iff_forallVerticalRepresentable :
    representableByAlgebraicSpaces f ↔ forallVerticalRepresentable f :=
  sorry

/-- Representability by algebraic spaces is equivalent to the existence of a
Definition 87.11.1 covering of `Y` and then of each `Y_ j ×_Y X` whose
projections `X_ ji ⟶ Y_ j` are representable by algebraic spaces. -/
theorem iff_existsCoverOnTarget :
    representableByAlgebraicSpaces f ↔ existsCoverOnTarget f :=
  sorry

/-- Representability by algebraic spaces is equivalent to the existence of a
Definition 87.11.1 covering of `X` factoring as `X_ i ⟶ Y_ i ⟶ Y` through
affine formal algebraic spaces with both legs representable by algebraic
spaces. -/
theorem iff_existsCoverOnSource :
    representableByAlgebraicSpaces f ↔ existsCoverOnSource f :=
  sorry

end representableByAlgebraicSpaces

end AlgebraicGeometry.ChosenBigFppfSite
