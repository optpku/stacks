module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object
public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.AbsoluteTransformations.Maps.Construction

/-!
# Scheme representability of automorphism groups

The automorphism group of a field-valued point of an algebraic stack is a
scheme under separation or quasi-finiteness hypotheses on the diagonal or
the absolute inertia projection, or when the stack is quasi-DM.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Inertia
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.automorphismGroup

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
  Iff.rfl

/-- If the automorphism group algebraic space of a field-valued point is a
scheme, then it is equivalent to the groupoid fibration of some algebraic space
that is a scheme. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (p : FieldValuedPoint X) :
    IsScheme p →
      ∃ G : AlgebraicSpace S,
        Nonempty (automorphismGroup p ≌ G.toGroupoids) ∧
          AlgebraicSpace.IsScheme G :=
  fun h ↦ h

/-- An equivalence with the groupoid fibration of an algebraic space that is a
scheme witnesses that the automorphism group algebraic space of a field-valued
point is a scheme. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {p : FieldValuedPoint X} {G : AlgebraicSpace S}
    (e : Nonempty (automorphismGroup p ≌ G.toGroupoids))
    (hG : AlgebraicSpace.IsScheme G) : IsScheme p :=
  ⟨G, e, hG⟩

/-- If the diagonal of an algebraic stack is quasi-separated, then the
automorphism group algebraic space of each field-valued point is a scheme. -/
theorem of_quasiSeparated_diagonal {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X)
    (h : Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
      (diagonal.{u + 1, u, u + 1} X)) :
    IsScheme p :=
  sorry

/-- If the diagonal of an algebraic stack is locally separated, then the
automorphism group algebraic space of each field-valued point is a scheme. -/
theorem of_locallySeparated_diagonal {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X)
    (h : Groupoids.Hom.has (@AlgebraicSpace.LocallySeparated S)
      (diagonal.{u + 1, u, u + 1} X)) :
    IsScheme p :=
  sorry

/-- The automorphism group algebraic space of each field-valued point of a
quasi-DM algebraic stack is a scheme. -/
theorem of_isQuasiDM {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsQuasiDM X] (p : FieldValuedPoint X) :
    IsScheme p :=
  sorry

/-- If the absolute inertia projection of an algebraic stack is
quasi-separated, then the automorphism group algebraic space of each
field-valued point is a scheme. -/
theorem of_quasiSeparated_inertia {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X)
    (h : Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
      (forget.{u + 1, u, u, u + 1} X)) :
    IsScheme p :=
  sorry

/-- If the absolute inertia projection of an algebraic stack is locally
separated, then the automorphism group algebraic space of each field-valued
point is a scheme. -/
theorem of_locallySeparated_inertia {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X)
    (h : Groupoids.Hom.has (@AlgebraicSpace.LocallySeparated S)
      (forget.{u + 1, u, u, u + 1} X)) :
    IsScheme p :=
  sorry

/-- If the absolute inertia projection of an algebraic stack is locally
quasi-finite, then the automorphism group algebraic space of each field-valued
point is a scheme. -/
theorem of_locallyQuasiFinite_inertia {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X)
    (h : Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
      (forget.{u + 1, u, u, u + 1} X)) :
    IsScheme p :=
  sorry

end IsScheme

end AlgebraicGeometry.AlgebraicStack.automorphismGroup
