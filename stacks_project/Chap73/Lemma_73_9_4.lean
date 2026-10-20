/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fpqc
import StacksCheckRecall

/-!
# Recognizing fpqc coverings of algebraic spaces after étale base change

An indexed family of morphisms of algebraic spaces with target `X` is an fpqc
covering if and only if its pullback along a surjective étale morphism from a
scheme is an fpqc covering.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 73.9.4: let `S` be a scheme and let `X` be an algebraic space over
`S`. Let `{f_i : X_i ⟶ X}` be a family of morphisms of algebraic spaces with
target `X`, and let `φ : ofOver U ⟶ X` be a surjective étale morphism from a
scheme. Then the family is an fpqc covering of `X` if and only if the pullback
family `{U ×_X X_i ⟶ U}` is an fpqc covering of `U`. -/
@[stacks 03MS] #check
  (AlgebraicGeometry.AlgebraicSpace.fpqcCovering_iff_pullback_surjectiveEtale :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
      (family : ι → Over X) {U : Over S} (φ : ofOver U ⟶ X)
      [Etale φ] [Surjective φ],
      FpqcCovering family ↔ FpqcCovering (pullbackFamily family φ))

end AlgebraicGeometry.AlgebraicSpace
