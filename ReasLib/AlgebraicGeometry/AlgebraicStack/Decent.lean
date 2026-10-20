module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiSeparated

/-!
# Decent algebraic stacks

An algebraic stack is decent when every point is represented by a
quasi-compact morphism from the spectrum of a field. Unlike algebraic
spaces, no monomorphism hypothesis is required.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic stack is decent if every point is represented by a
quasi-compact morphism from the spectrum of a field. -/
@[mk_iff]
class IsDecent {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : Prop where
  /-- Every point arises from a quasi-compact morphism `Spec(K) ⟶ X`. -/
  exists_quasiCompact :
    ∀ x : Points X, ∃ p : FieldValuedPoint X, QuasiCompact p.hom ∧ Points.mk p = x

namespace IsDecent

/-- A decent algebraic stack has, at every point, a quasi-compact morphism from
the spectrum of a field representing that point. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsDecent X] :
    ∀ x : Points X, ∃ p : FieldValuedPoint X,
      QuasiCompact p.hom ∧ Points.mk p = x :=
  sorry

/-- A choice of quasi-compact morphism `Spec(K) ⟶ X` at every point witnesses
that the algebraic stack is decent. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : ∀ x : Points X, ∃ p : FieldValuedPoint X,
      QuasiCompact p.hom ∧ Points.mk p = x) :
    IsDecent X :=
  sorry

end IsDecent

/-- The canonical slice of a scheme over `S` is a decent algebraic stack. -/
instance instIsDecent_slice {S : Scheme.{u}} (U : Over S) :
    IsDecent (GroupoidsOver.slice U) :=
  sorry

/-- The groupoid fibration of a decent algebraic space is a decent algebraic
stack. -/
instance instIsDecent_of_toGroupoids {S : Scheme.{u}} (A : AlgebraicSpace S)
    [AlgebraicSpace.IsDecent A] : IsDecent A.toGroupoids :=
  sorry

/-- A quasi-separated algebraic stack is decent. -/
instance instIsDecent_of_isQuasiSeparated {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiSeparated X] : IsDecent X :=
  sorry

/-- An algebraic stack with quasi-compact absolute diagonal is decent. -/
theorem IsDecent.of_quasiCompact_diagonal {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))) :
    IsDecent X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
