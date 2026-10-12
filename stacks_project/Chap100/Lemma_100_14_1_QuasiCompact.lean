/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Quasi-compact field-valued points of an algebraic stack

A morphism `Spec(k) ⟶ X` is quasi-compact in the sense of Section 100.3 when
the corresponding field-valued point has the algebraic-space quasi-compactness
property. The two tests at a point `x ∈ |X|` are existence of one such
representative and quasi-compactness of every representative in that class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace FieldValuedPoint

/-- A field-valued point `p` given by `Spec(k) ⟶ X` is quasi-compact when the
1-morphism `p.hom` has the algebraic-space quasi-compactness property in the
sense of Section 100.3. -/
def quasiCompact {S : Scheme.{u}} {X : GroupoidsOver S} (p : FieldValuedPoint X) :
    Prop :=
  Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) p.hom

/-- Quasi-compactness of a field-valued point is the Section 100.3 property
`has` of `p.hom` for algebraic-space quasi-compactness. -/
theorem quasiCompact_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    (p : FieldValuedPoint X) :
    p.quasiCompact ↔ Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) p.hom :=
  sorry

/-- A field-valued point of an algebraic stack is representable by algebraic
spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X) :
    relativelyRepresentableByAlgebraicSpaces p.hom :=
  sorry

/-- Quasi-compactness of field-valued points is preserved along a factorization
by a field extension. -/
theorem Factorization.has_quasiCompact {S : Scheme.{u}} {X : GroupoidsOver S}
    {p q : FieldValuedPoint X} (φ : Factorization p q) :
    p.quasiCompact ↔ q.quasiCompact :=
  sorry

/-- Quasi-compactness of field-valued points is preserved by common field
extensions. -/
theorem Equivalent.has_quasiCompact {S : Scheme.{u}} {X : GroupoidsOver S}
    {p q : FieldValuedPoint X} (h : Equivalent p q) :
    p.quasiCompact ↔ q.quasiCompact :=
  sorry

end FieldValuedPoint

/-- There is a quasi-compact morphism from the spectrum of a field in the
equivalence class of `x`. -/
def existsQuasiCompactFieldValuedPoint {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) : Prop :=
  ∃ p : FieldValuedPoint X, p.quasiCompact ∧ Points.mk p = x

/-- `existsQuasiCompactFieldValuedPoint X x` unpacks to a quasi-compact morphism
from the spectrum of a field in the class of `x`. -/
theorem existsQuasiCompactFieldValuedPoint_iff {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    existsQuasiCompactFieldValuedPoint X x ↔
      ∃ p : FieldValuedPoint X, p.quasiCompact ∧ Points.mk p = x :=
  sorry

namespace existsQuasiCompactFieldValuedPoint

/-- A quasi-compact morphism `Spec(k) ⟶ X` in the class of `x` witnesses
`existsQuasiCompactFieldValuedPoint`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (p : FieldValuedPoint X) (hp : p.quasiCompact)
    (hx : Points.mk p = x) : existsQuasiCompactFieldValuedPoint X x :=
  sorry

/-- `existsQuasiCompactFieldValuedPoint X x` supplies a quasi-compact morphism
from the spectrum of a field in the class of `x`. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : existsQuasiCompactFieldValuedPoint X x) :
    ∃ p : FieldValuedPoint X, p.quasiCompact ∧ Points.mk p = x :=
  sorry

end existsQuasiCompactFieldValuedPoint

/-- Every field-valued point in the class of `x` is a quasi-compact morphism. -/
def forallFieldValuedPointQuasiCompact {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] (x : Points X) : Prop :=
  ∀ p : FieldValuedPoint X, Points.mk p = x → p.quasiCompact

/-- `forallFieldValuedPointQuasiCompact X x` unpacks to quasi-compactness of every
field-valued point in the class of `x`. -/
theorem forallFieldValuedPointQuasiCompact_iff {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X) :
    forallFieldValuedPointQuasiCompact X x ↔
      ∀ p : FieldValuedPoint X, Points.mk p = x → p.quasiCompact :=
  sorry

namespace forallFieldValuedPointQuasiCompact

/-- A universal quasi-compactness condition on field-valued points in the class of
`x` witnesses `forallFieldValuedPointQuasiCompact`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X}
    (h : ∀ p : FieldValuedPoint X, Points.mk p = x → p.quasiCompact) :
    forallFieldValuedPointQuasiCompact X x :=
  sorry

/-- Under `forallFieldValuedPointQuasiCompact X x`, every field-valued point in
the class of `x` is quasi-compact. -/
theorem spec {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : Points X} (h : forallFieldValuedPointQuasiCompact X x)
    {p : FieldValuedPoint X} (hp : Points.mk p = x) : p.quasiCompact :=
  sorry

end forallFieldValuedPointQuasiCompact

end AlgebraicGeometry.AlgebraicStack
