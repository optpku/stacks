/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap87.Lemma_87_27_4_Local

/-!
# Characterizations of closed immersions of formal algebraic spaces

Lemma 87.27.4 records that a morphism of formal algebraic spaces is a closed
immersion iff this is tested by closed-immersion projections after
scheme-valued and affine base change, by a Definition 87.11.1 étale atlas of
the target, and by a representable fppf morphism of formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace ClosedImmersion

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)

/-- Lemma 87.27.4: for a morphism `f : X ⟶ Y` of formal algebraic spaces over a
scheme `S`, the following are equivalent: `ClosedImmersion f`; every
scheme-valued base change of `f` is a closed immersion (`forallScheme f`);
every affine-scheme-valued base change of `f` is a closed immersion
(`forallAffine f`); some covering `{Y_j ⟶ Y}` as in Definition 87.11.1 has
each base change `X ×_Y Y_j ⟶ Y_j` a closed immersion
(`existsCoverOnTarget f`); and some morphism `Z ⟶ Y` of formal algebraic
spaces that is representable by algebraic spaces, surjective, flat, and
locally of finite presentation has `X ×_Y Z ⟶ Z` a closed immersion
(`existsFppf f`). -/
@[stacks 0GHY]
theorem tfae :
    List.TFAE [ClosedImmersion f, forallScheme f, forallAffine f,
      existsCoverOnTarget f, existsFppf f] := sorry

/-- A morphism of formal algebraic spaces is a closed immersion iff every
scheme-valued base change has closed-immersion projection. -/
theorem iff_forallScheme : ClosedImmersion f ↔ forallScheme f := sorry

/-- A morphism of formal algebraic spaces is a closed immersion iff every
affine-scheme-valued base change has closed-immersion projection. -/
theorem iff_forallAffine : ClosedImmersion f ↔ forallAffine f := sorry

/-- A morphism of formal algebraic spaces is a closed immersion iff some
Definition 87.11.1 covering of the target has closed-immersion pullbacks of
`f`. -/
theorem iff_existsCoverOnTarget : ClosedImmersion f ↔ existsCoverOnTarget f :=
  sorry

/-- A morphism of formal algebraic spaces is a closed immersion iff some
representable fppf morphism of formal algebraic spaces to the target has
closed-immersion pullbacks `X ×_Y Z ⟶ Z`. -/
theorem iff_existsFppf : ClosedImmersion f ↔ existsFppf f := sorry

end ClosedImmersion

end AlgebraicGeometry.FormalAlgebraicSpace
