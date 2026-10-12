/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.Section
import StacksCheckRecall

/-!
# Lemma 29.6.8

The scheme-theoretic image of a section of a separated morphism agrees with the target over
the retrocompact open on which the section is defined.

@stack 0CNG
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 29.6.8: for a section over a retrocompact open of a separated morphism, the
scheme-theoretic image maps isomorphically to the target over that open. -/
@[stacks 0CNG] #check
  (AlgebraicGeometry.schemeTheoreticImage_section_restrict_isIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] (V : Y.Opens)
      (_ : IsRetrocompact (V : Set Y)) (s : (V : Scheme.{u}) ⟶ X)
      (_ : s ≫ f = V.ι),
      IsIso ((Scheme.Hom.imageι s ≫ f) ∣_ V))
