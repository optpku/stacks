/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_47_7_Irreducible
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap70.Lemma_70_17_1_MinimalNonscheme

/-!
# Minimal nonschemes are reduced and irreducible

A quasi-compact quasi-separated algebraic space that is not a scheme, while
every proper closed subspace is a scheme, is reduced and irreducible.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsReduced

/-- Lemma 70.17.2 (1): Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. Quasi-separatedness is absolute
(Stacks Definition 66.3.1). Assume that every proper closed subspace `Z ⊂ X`
is a scheme, but `X` is not a scheme. Then `X` is reduced. A closed subspace
of `X` is proper when its inclusion is not an isomorphism. -/
@[stacks 0B7Z]
theorem of_isMinimalNonscheme {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (hX : IsMinimalNonscheme X) : IsReduced X :=
  sorry

end IsReduced

namespace IsIrreducible

/-- Lemma 70.17.2 (2): Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. Quasi-separatedness is absolute
(Stacks Definition 66.3.1). Assume that every proper closed subspace `Z ⊂ X`
is a scheme, but `X` is not a scheme. Then `X` is irreducible. A closed
subspace of `X` is proper when its inclusion is not an isomorphism. -/
@[stacks 0B7Z]
theorem of_isMinimalNonscheme {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (hX : IsMinimalNonscheme X) : IsIrreducible X :=
  sorry

end IsIrreducible

end AlgebraicGeometry.AlgebraicSpace
