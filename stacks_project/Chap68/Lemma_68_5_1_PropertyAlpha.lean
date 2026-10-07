module

public import stacks_project.Chap68.Lemma_68_4_2_Fibre

/-!
# Property (α) for algebraic spaces

An algebraic space has property (α) when every point satisfies the affine étale
finite-fibre test of Lemma 68.4.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space has property (α) if every étale morphism from an affine
scheme has finite fibre over every point. -/
@[mk_iff]
class HasPropertyAlpha {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- Affine étale morphisms from schemes into `X` have finite fibre over every
  point of `|X|`. -/
  finiteFibre : ∀ x : Points X, forallAffineEtaleFiniteFibre X x

namespace HasPropertyAlpha

/-- An algebraic space with property (α) has finite affine étale fibres over
every point. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [HasPropertyAlpha X] :
    ∀ x : Points X, forallAffineEtaleFiniteFibre X x :=
  sorry

/-- The affine étale finite-fibre test at every point witnesses property (α). -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ x : Points X, forallAffineEtaleFiniteFibre X x) :
    HasPropertyAlpha X :=
  sorry

end HasPropertyAlpha

/-- A scheme over `S`, viewed as an algebraic space, has property (α). -/
instance instHasPropertyAlpha_ofOver {S : Scheme.{u}} (T : Over S) :
    HasPropertyAlpha (ofOver T) :=
  sorry

/-- Property (α) is equivalent to existence of an étale scheme covering with
finite fibres over every point. -/
theorem hasPropertyAlpha_iff_existsEtaleCoverFiniteFibre {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    HasPropertyAlpha X ↔ ∀ x : Points X, existsEtaleCoverFiniteFibre X x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
