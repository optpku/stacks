module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.LocallyPrincipal.Complement
public import stacks_project.Chap71.Definition_71_6_1_LocallyPrincipal

/-!
# Complements of locally principal closed subspaces

The open complement of a locally principal closed subspace of an algebraic space
is an affine morphism into the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.6.3: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If `i : Z ⟶ X` is a locally principal closed subspace, then the open complement
inclusion `closedImmersionComplementι i : closedImmersionComplement i ⟶ X` is
an affine morphism of algebraic spaces. -/
@[stacks 083D] #check
  (AlgebraicGeometry.AlgebraicSpace.IsLocallyPrincipal.affine_closedImmersionComplementι :
    ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X)
      [IsLocallyPrincipalClosedSubspace i],
      Affine (closedImmersionComplementι i))
