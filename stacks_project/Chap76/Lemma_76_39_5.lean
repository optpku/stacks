/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Domination
import StacksCheckRecall

/-!
# Domination of proper modifications of algebraic spaces by admissible blowups

A proper morphism of algebraic spaces that is an isomorphism over a
quasi-compact open of a qcqs base is dominated by a `U`-admissible blowup.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.39.5: Let `S` be a scheme. Let `f : X ⟶ B` be a morphism of
algebraic spaces over `S`. Let `U ⊂ B` be an open subspace. Assume `B` is
quasi-compact and quasi-separated, `U` is quasi-compact, `f : X ⟶ B` is proper,
and `f⁻¹(U) ⟶ U` is an isomorphism. Then there exists a `U`-admissible blowup
`B' ⟶ B` which dominates `X`, i.e. such that there exists a factorization
`B' ⟶ X ⟶ B` of the blowup morphism. -/
@[stacks 087G] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_isAdmissibleBlowup_dominating :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
      (f : X ⟶ B) [Proper f]
      (U : OpenSubspace B) [IsQuasiCompact U.X]
      [IsIso (pullback.snd f U.ι)],
    ∃ (B' : AlgebraicSpace S) (b : B' ⟶ B) (g : B' ⟶ X),
      IsAdmissibleBlowup U b ∧ g ≫ f = b)
