/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap71.Definition_71_6_1_LocallyPrincipal

/-!
# Complements of locally principal closed subspaces

The open complement of a locally principal closed subspace of an algebraic space
is an affine morphism into the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsLocallyPrincipalClosedSubspace

/-- Lemma 71.6.3: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If `i : Z ⟶ X` is a locally principal closed subspace, then the open complement
inclusion `closedImmersionComplementι i : closedImmersionComplement i ⟶ X` is
an affine morphism of algebraic spaces. -/
@[stacks 083D]
instance affine_closedImmersionComplementι {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsLocallyPrincipalClosedSubspace i] :
    Affine (closedImmersionComplementι i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsLocallyPrincipalClosedSubspace
