/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.InvariantSpectrum
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-!
# Invariant spectra mapping to presented algebraic stacks

Effective descent of a presentation atlas gives a morphism from an invariant spectrum to
an algebraic stack equipped with that presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {Z : GroupoidsOver S} [AlgebraicStack Z]
variable (P G : GroupoidScheme S)
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (tSharp : A →+* B)
variable (eU : Spec (CommRingCat.of A) ≅ P.U.left)
variable (eR : Spec (CommRingCat.of B) ≅ P.R.left)
variable
  (h_source : eR.hom ≫ P.s.left =
    Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ eU.hom)
variable
  (h_target : eR.hom ≫ P.t.left =
    Spec.map (CommRingCat.ofHom tSharp) ≫ eU.hom)
variable [IsFiniteLocallyFree P.s.left] [IsFiniteLocallyFree P.t.left]
variable [IsEquivalenceRelation P.t P.s]
variable (hU : P.U = G.U)

/-- The invariant-spectrum morphism to a presented algebraic stack, obtained by composing
the descended quotient-atlas morphism with the presentation equivalence. -/
def etaleCovering
    (ι : GroupoidScheme.Hom P G) (hι : ι.IsIdentityOnObjects hU)
    (f_can : (SmallQuotient.quotientStack (ofScheme G)) ⟶ Z)
    [(toBasedFunctor f_can).IsEquivalence] :
    GroupoidsOver.slice (invariantSpectrum P tSharp eU eR h_source h_target) ⟶ Z :=
  invariantSpectrumToQuotient P G tSharp eU eR h_source h_target hU ι hι ≫ f_can

/-- The covering factors the atlas of `[U/R]` through the invariant-spectrum
quotient of P and then applies the equivalence `f_can`. -/
theorem etaleCovering_spec
    (ι : GroupoidScheme.Hom P G) (hι : ι.IsIdentityOnObjects hU)
    (f_can : (SmallQuotient.quotientStack (ofScheme G)) ⟶ Z)
    [(toBasedFunctor f_can).IsEquivalence] :
    Nonempty
      (overMap (GroupoidScheme.invariantSpectrumQuotient P tSharp eU eR h_source h_target) ≫
          etaleCovering P G tSharp eU eR h_source h_target hU ι hι f_can ≅
        atlasFromSlice_eqToHom P G hU ≫ f_can) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
