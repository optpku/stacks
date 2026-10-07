module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Lemma_66_16_3_Local

/-!
# Characterizations of étale morphisms of algebraic spaces

Lemma 66.16.3 records that étale-ness of a morphism of algebraic spaces is
equivalent to the source-atlas, target-atlas, and commutative-square tests.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Etale

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 66.16.3: for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `Etale f`; some surjective étale scheme atlas
of `X` whose composite with `f` is étale as algebraic spaces; some surjective
étale scheme atlas of `Y` along which the base change of `f` is étale as
algebraic spaces; and some commutative square of schemes over `f` with étale
vertical arrows, surjective left vertical arrow, and étale horizontal arrow. -/
@[stacks 03FS]
theorem tfae :
    List.TFAE [Etale f, existsOnSource f, existsOnTarget f, existsSquare f] := sorry

/-- A morphism of algebraic spaces is étale iff some surjective étale scheme
atlas of the source has étale composite with `f`. -/
theorem iff_existsOnSource : Etale f ↔ existsOnSource f := sorry

/-- A morphism of algebraic spaces is étale iff some surjective étale scheme
atlas of the target has étale pullback of `f`. -/
theorem iff_existsOnTarget : Etale f ↔ existsOnTarget f := sorry

/-- A morphism of algebraic spaces is étale iff some commutative square of
scheme atlases over `f` has étale vertical arrows, surjective left vertical
arrow, and étale horizontal arrow. -/
theorem iff_existsSquare : Etale f ↔ existsSquare f := sorry

end Etale

end AlgebraicGeometry.AlgebraicSpace
