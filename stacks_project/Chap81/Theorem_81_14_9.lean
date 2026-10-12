/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap81.Lemma_81_14_7_Compactification

/-!
# Theorem 81.14.9

A separated finite-type algebraic space over a quasi-compact quasi-separated
algebraic space has a compactification over that base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace HasCompactification

/-- Theorem 81.14.9. Let `S` be a scheme. Let `B` be a quasi-compact and
quasi-separated algebraic space over `S`. Let `X ⟶ B` be a separated, finite
type morphism. Then `X` has a compactification over `B`. -/
@[stacks 0F4D]
instance of_finiteType {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [IsQuasiCompact B] [IsAbsolutelyQuasiSeparated B]
    (f : X ⟶ B) [FiniteType f] [Separated f] :
    HasCompactification f :=
  sorry

end HasCompactification

end AlgebraicGeometry.AlgebraicSpace
