module

public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap101.Lemma_101_19_2_AutomorphismGroup

/-!
# Scheme-ness of automorphism group algebraic spaces

The automorphism group object of a field-valued point of an algebraic stack is
a scheme when it is equivalent to the groupoid fibration of an algebraic space
that is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace automorphismGroup

/-- The automorphism group algebraic space of a field-valued point is a scheme
if it is equivalent to the groupoid fibration of an algebraic space over `S`
that is a scheme. -/
def IsScheme {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (p : FieldValuedPoint X) : Prop :=
  ∃ G : AlgebraicSpace S,
    Nonempty (automorphismGroup p ≌ G.toGroupoids) ∧ AlgebraicSpace.IsScheme G

namespace IsScheme

/-- The automorphism group algebraic space of a field-valued point is a scheme
if and only if it is equivalent to the groupoid fibration of an algebraic space
that is a scheme. -/
theorem iff {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (p : FieldValuedPoint X) :
    IsScheme p ↔
      ∃ G : AlgebraicSpace S,
        Nonempty (automorphismGroup p ≌ G.toGroupoids) ∧
          AlgebraicSpace.IsScheme G :=
  sorry

/-- If the automorphism group algebraic space of a field-valued point is a
scheme, then it is equivalent to the groupoid fibration of some algebraic space
that is a scheme. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (p : FieldValuedPoint X) :
    IsScheme p →
      ∃ G : AlgebraicSpace S,
        Nonempty (automorphismGroup p ≌ G.toGroupoids) ∧
          AlgebraicSpace.IsScheme G :=
  sorry

/-- An equivalence with the groupoid fibration of an algebraic space that is a
scheme witnesses that the automorphism group algebraic space of a field-valued
point is a scheme. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {p : FieldValuedPoint X} {G : AlgebraicSpace S}
    (e : Nonempty (automorphismGroup p ≌ G.toGroupoids))
    (hG : AlgebraicSpace.IsScheme G) : IsScheme p :=
  sorry

end IsScheme

/-- The automorphism group object of a field-valued point of an algebraic stack
is representable by an algebraic space. -/
theorem isRepresentableByAlgebraicSpace {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X) :
    IsRepresentableByAlgebraicSpace (automorphismGroup p) :=
  sorry

end automorphismGroup

end AlgebraicGeometry.AlgebraicStack
