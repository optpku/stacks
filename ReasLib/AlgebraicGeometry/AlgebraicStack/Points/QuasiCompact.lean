/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Quasi-compact field-valued representatives of points

For an algebraic stack, quasi-compactness of a field-valued representative is
invariant under field extension and hence depends only on its point class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace FieldValuedPoint

/-- A field-valued point is quasi-compact when every algebraic-space morphism
representing a scheme base change of its morphism is quasi-compact. -/
def quasiCompact {S : Scheme.{u}} {X : GroupoidsOver S} (p : FieldValuedPoint X) :
    Prop :=
  Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) p.hom

/-- Quasi-compactness of a field-valued point is the algebraic-space
quasi-compactness property of its morphism. -/
theorem quasiCompact_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    (p : FieldValuedPoint X) :
    p.quasiCompact ↔ Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) p.hom :=
  Iff.rfl

/-- A field-valued point of an algebraic stack is representable by algebraic
spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X) :
    relativelyRepresentableByAlgebraicSpaces p.hom :=
  sorry

/-- Quasi-compactness of field-valued points of an algebraic stack is invariant
under a factorization by a field extension. -/
theorem Factorization.has_quasiCompact {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {p q : FieldValuedPoint X} (φ : Factorization p q) :
    p.quasiCompact ↔ q.quasiCompact :=
  sorry

/-- Field-valued points of an algebraic stack admitting a common field
extension have equivalent quasi-compactness conditions. -/
theorem Equivalent.has_quasiCompact {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {p q : FieldValuedPoint X} (h : Equivalent p q) :
    p.quasiCompact ↔ q.quasiCompact :=
  sorry

end FieldValuedPoint

/-- There is a quasi-compact morphism from the spectrum of a field in the
equivalence class of `x`. -/
def existsQuasiCompactFieldValuedPoint {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) : Prop :=
  ∃ p : FieldValuedPoint X, p.quasiCompact ∧ Points.mk p = x

/-- Existence of a quasi-compact representative is equivalent to existence of a
quasi-compact field-valued point whose class is `x`. -/
theorem existsQuasiCompactFieldValuedPoint_iff {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    existsQuasiCompactFieldValuedPoint X x ↔
      ∃ p : FieldValuedPoint X, p.quasiCompact ∧ Points.mk p = x :=
  Iff.rfl

namespace existsQuasiCompactFieldValuedPoint

/-- A quasi-compact field-valued point with class `x` gives a quasi-compact
representative of `x`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (p : FieldValuedPoint X) (hp : p.quasiCompact)
    (hx : Points.mk p = x) : existsQuasiCompactFieldValuedPoint X x :=
  ⟨p, hp, hx⟩

/-- Existence of a quasi-compact representative supplies a quasi-compact
field-valued point in the specified class. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : existsQuasiCompactFieldValuedPoint X x) :
    ∃ p : FieldValuedPoint X, p.quasiCompact ∧ Points.mk p = x :=
  h

end existsQuasiCompactFieldValuedPoint

/-- Every field-valued point in the class of `x` is a quasi-compact morphism. -/
def forallFieldValuedPointQuasiCompact {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) : Prop :=
  ∀ p : FieldValuedPoint X, Points.mk p = x → p.quasiCompact

/-- Quasi-compactness of all representatives of `x` is equivalent to
quasi-compactness of each field-valued point with class `x`. -/
theorem forallFieldValuedPointQuasiCompact_iff {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    forallFieldValuedPointQuasiCompact X x ↔
      ∀ p : FieldValuedPoint X, Points.mk p = x → p.quasiCompact :=
  Iff.rfl

namespace forallFieldValuedPointQuasiCompact

/-- Quasi-compactness of each field-valued point with class `x` implies the
universal quasi-compactness condition at `x`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X}
    (h : ∀ p : FieldValuedPoint X, Points.mk p = x → p.quasiCompact) :
    forallFieldValuedPointQuasiCompact X x :=
  h

/-- The universal quasi-compactness condition at `x` makes every field-valued
point in the class of `x` quasi-compact. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : forallFieldValuedPointQuasiCompact X x)
    {p : FieldValuedPoint X} (hp : Points.mk p = x) : p.quasiCompact :=
  h p hp

end forallFieldValuedPointQuasiCompact

/-- A point of an algebraic stack has a quasi-compact field-valued representative
if and only if every field-valued representative of that point is quasi-compact. -/
theorem existsQuasiCompactFieldValuedPoint_iff_forall
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    existsQuasiCompactFieldValuedPoint X x ↔
      forallFieldValuedPointQuasiCompact X x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
