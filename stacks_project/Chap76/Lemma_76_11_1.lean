/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Thickening
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening

variable {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X')
variable [IsFirstOrderThickening i]
variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology X') AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 2}
  (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasExt.{u + 2}
  (Sheaf (smallEtaleTopology X') AddCommGrpCat.{u + 1})]

/- Lemma 76.11.1: a first-order thickening `i : X ⟶ X'` of algebraic spaces
over a scheme `S`, with ideal sheaf `I`, has the canonical exact sequence of
abelian groups
`0 ⟶ H⁰(X, I) ⟶ H⁰(X', 𝒪_{X'}ˣ) ⟶ H⁰(X, 𝒪_Xˣ) ⟶ H¹(X, I) ⟶
  Pic(X') ⟶ Pic(X) ⟶ H²(X, I) ⟶ ⋯`. -/
@[stacks 0DNM] #check
  (AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening.picardCohomologySequence_longExact i :
    (AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening.picardCohomologySequence i).Exact ∧
      ∀ n : ℕ, (AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening.unitsWindow i n).Exact)

end AlgebraicGeometry.AlgebraicSpace.IsFirstOrderThickening
