/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.EffectiveEpi
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

/- Lemma 35.13.4: if every base change of a family of scheme morphisms to an affine scheme is
effective epimorphic, then the original family is universally effective epimorphic. -/
@[stacks 0EUC] #check
  (CategoryTheory.SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily.of_affine :
    ∀ {X : Scheme.{u}} (K : CategoryTheory.SemiRepresentableFamily.Over.{v} X),
      (∀ (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X),
        CategoryTheory.SemiRepresentableFamily.Over.IsEffectiveEpiFamily (K.baseChange f)) →
      CategoryTheory.SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily K)
