/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme.Stalk
import StacksCheckRecall

/-!
# Obtaining a scheme from stalkwise base changes

A quasi-compact quasi-separated algebraic space over a scheme is itself a scheme
once every base change to the spectrum of the stalk of the base at the image of
a point is a scheme.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 70.17.3: Let `f : X ⟶ S` be a quasi-compact and quasi-separated
morphism from an algebraic space to a scheme `S`. If for every `x : Points X`
with image `s = f(x)` the algebraic space `X ×_S Spec(𝒪_{S,s})` is a scheme,
then `X` is a scheme. Here `f` is the structure morphism `SchemeRealization.toBase X`,
`s` is `Points.base x`, and `X ×_S Spec(𝒪_{S,s})` is
`baseChange (S.fromSpecStalk s) X`. -/
@[stacks 0B80] #check
  (AlgebraicGeometry.AlgebraicSpace.isScheme_of_forall_isScheme_baseChange_fromSpecStalk :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [QuasiCompact (SchemeRealization.toBase X)]
      [QuasiSeparated (SchemeRealization.toBase X)],
      (∀ x : Points X,
        IsScheme (baseChange (S.fromSpecStalk (Points.base x)) X)) →
      IsScheme X)

end AlgebraicGeometry.AlgebraicSpace
