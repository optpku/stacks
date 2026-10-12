/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap87.Lemma_87_26_4_Mono

/-!
# Characterizations of monomorphisms of formal algebraic spaces

Lemma 87.26.4 records that a morphism of formal algebraic spaces is a
monomorphism iff this is tested by monomorphic projections after scheme-valued
and affine base change, by a Definition 87.11.1 étale atlas of the target, by a
jointly fppf-locally surjective family, and by a representable fppf morphism of
formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Monomorphisms

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)

/-- Lemma 87.26.4: for a morphism `f : X ⟶ Y` of formal algebraic spaces over a
scheme `S`, the following are equivalent: `Mono f`; every scheme-valued base
change of `f` is a monomorphism (`forallScheme f`); every affine-scheme-valued
base change of `f` is a monomorphism (`forallAffine f`); some covering
`{Y_j ⟶ Y}` as in Definition 87.11.1 has each base change `X ×_Y Y_j ⟶ Y_j` a
monomorphism (`existsCoverOnTarget f`); some family `{Y_j ⟶ Y}` whose coproduct
map is an fppf sheaf surjection has each `X ×_Y Y_j ⟶ Y_j` a monomorphism
(`existsSheafSurjection f`); and some morphism `Z ⟶ Y` of formal algebraic
spaces that is representable by algebraic spaces, surjective, flat, and locally
of finite presentation has `X ×_Y Z ⟶ Z` a monomorphism (`existsFppf f`). -/
@[stacks 0GHV]
theorem tfae :
    List.TFAE [Mono f, forallScheme f, forallAffine f, existsCoverOnTarget f,
      existsSheafSurjection f, existsFppf f] :=
  sorry

/-- A morphism of formal algebraic spaces is a monomorphism iff every
scheme-valued base change has monomorphic projection. -/
theorem iff_forallScheme : Mono f ↔ forallScheme f := sorry

/-- A morphism of formal algebraic spaces is a monomorphism iff every
affine-scheme-valued base change has monomorphic projection. -/
theorem iff_forallAffine : Mono f ↔ forallAffine f := sorry

/-- A morphism of formal algebraic spaces is a monomorphism iff some Definition
87.11.1 covering of the target has monomorphic pullbacks of `f`. -/
theorem iff_existsCoverOnTarget : Mono f ↔ existsCoverOnTarget f := sorry

/-- A morphism of formal algebraic spaces is a monomorphism iff some jointly
fppf-locally surjective family has monomorphic pullbacks of `f`. -/
theorem iff_existsSheafSurjection : Mono f ↔ existsSheafSurjection f := sorry

/-- A morphism of formal algebraic spaces is a monomorphism iff some
representable fppf morphism of formal algebraic spaces to the target has
monomorphic pullbacks of `f`. -/
theorem iff_existsFppf : Mono f ↔ existsFppf f := sorry

end Monomorphisms

end AlgebraicGeometry.FormalAlgebraicSpace
