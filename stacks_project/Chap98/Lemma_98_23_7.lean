/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.NaiveObstructionTheory.Openness
import StacksCheckRecall

/-!
# Lemma 98.23.7

A category fibred in groupoids over a locally Noetherian base, satisfying
(RS*) and equipped with a naive obstruction theory whose complexes `E_x`
have finitely generated cohomology on finite-type algebras, satisfies
openness of versality.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver

universe u

/- Lemma 98.23.7. Let `S` be a locally Noetherian scheme. Let `X` be a
category fibred in groupoids over `(Sch/S)_fppf`. Assume that `X` satisfies
(RS*) and that `X` has a naive obstruction theory. Then openness of versality
holds for `X` provided the complexes `E_x` of Definition 98.23.5 have finitely
generated cohomology groups for pairs `(A, x)` where `A` is of finite type over
`S`. -/
@[stacks 07YU] #check
  (AlgebraicGeometry.GroupoidsOver.OpennessOfVersality.ofNaiveObstructionTheory :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
      [HasStrongRimSchlessinger X] (𝒪 : NaiveObstructionTheory X),
      𝒪.hasFiniteCohomology → OpennessOfVersality X)
