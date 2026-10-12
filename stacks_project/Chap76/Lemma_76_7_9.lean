/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap76.Definition_76_7_2_Differentials

/-!
Local source erratum for tag 05Z9: the pinned source prints `Ω_{X/S} = 0` for
an immersion `f : X ⟶ Y` over `S`. Its proof, via tag 01UY and étale localization
(04CU), instead gives `Ω_{X/Y} = 0`. The printed formula fails for the identity
immersion of the affine line over a field. We retain the original source and
explicitly use the differentials of `f`, with no additional hypothesis.

The differentials are the common owner from Definition 76.7.2, also used by
Lemma 76.7.3; no parallel reconstruction or zero-object definition is introduced.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Lemma 76.7.9, with the explicit local subscript erratum above: the sheaf of
relative differentials `Ω_{X/Y}` of an immersion `f : X ⟶ Y` is zero. -/
@[stacks 05Z9]
theorem isZero_relativeDifferentials_of_isImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsImmersion f] :
    IsZero (relativeDifferentials f) :=
  sorry

/-- The sheaf of relative differentials of a monomorphism of algebraic spaces vanishes. -/
theorem isZero_relativeDifferentials_of_mono {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Mono f] :
    IsZero (relativeDifferentials f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
