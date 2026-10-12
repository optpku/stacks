/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Definition_98_5_1
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
import Mathlib.Tactic.CrossRefAttribute

/-!
# Algebraic stacks satisfy the Rim-Schlessinger condition

An algebraic stack over a locally Noetherian scheme satisfies condition (RS).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Lemma 98.5.2: an algebraic stack over a locally Noetherian scheme `S`
satisfies condition (RS). -/
@[stacks 07WQ]
instance instHasRimSchlessinger_algebraicStack {S : Scheme.{u}}
    [IsLocallyNoetherian S] (X : GroupoidsOver S) [AlgebraicStack X] :
    HasRimSchlessinger X := sorry

end AlgebraicGeometry.GroupoidsOver
