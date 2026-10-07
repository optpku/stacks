module

public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Residue fields of decent algebraic spaces

On a decent algebraic space, every point is represented by a quasi-compact monomorphism
from the spectrum of a field. The residue field at that point is the source field of a
chosen such representative, unique up to unique factorization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace FieldValuedPoint

/-- The chosen field-valued point `Spec(κ(x)) ⟶ X` representing a point of a decent
algebraic space. -/
def residuePoint {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] (x : Points X) :
    FieldValuedPoint X :=
  (IsDecent.exists_quasiCompact_mono x).choose

/-- The chosen residue-field point is a quasi-compact monomorphism representing `x`. -/
theorem residuePoint_spec {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) :
    QuasiCompact (residuePoint x).hom ∧ Mono (residuePoint x).hom ∧
      Points.mk (residuePoint x) = x :=
  sorry

/-- The chosen residue-field point represents `x`. -/
theorem mk_residuePoint {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) : Points.mk (residuePoint x) = x :=
  sorry

/-- A field-valued point representing the same point as a monomorphic field-valued point
factors uniquely through it. -/
theorem unique_factorization_of_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    {p q : FieldValuedPoint X} (hq : Mono q.hom) (h : Points.mk p = Points.mk q) :
    Nonempty (p.Factorization q) ∧ Subsingleton (p.Factorization q) :=
  sorry

/-- Any field-valued point representing `x` factors uniquely through the residue-field
point. -/
theorem unique_factorization_residuePoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {x : Points X} (p : FieldValuedPoint X) (hp : Points.mk p = x) :
    Nonempty (p.Factorization (residuePoint x)) ∧
      Subsingleton (p.Factorization (residuePoint x)) :=
  sorry

/-- On a scheme over `S`, the algebraic-space residue-field point is equivalent to the
scheme residue-field point. -/
theorem residuePoint_ofOver {S : Scheme.{u}} (T : Over S) (t : T.left) :
    Equivalent (residuePoint (ofOver.pointsEquiv T t))
      (ofScheme (Scheme.FieldValuedPoint.residuePoint t)) :=
  sorry

end FieldValuedPoint

/-- The residue field of a decent algebraic space `X` at a point `x`. -/
abbrev residueField {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X) :
    CommRingCat :=
  .of (FieldValuedPoint.residuePoint x).K

/-- The residue field is the source field of the chosen residue-field point. -/
theorem residueField_eq {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) :
    X.residueField x = .of (FieldValuedPoint.residuePoint x).K :=
  sorry

/-- The residue field of a decent algebraic space is a field. -/
instance instField_residueField {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : Field (X.residueField x) :=
  (FieldValuedPoint.residuePoint x).field

/-- The monomorphism `Spec(κ(x)) ⟶ X` of algebraic spaces over `S`. -/
abbrev fromSpecResidueField {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : ofOver (FieldValuedPoint.residuePoint x).overObj ⟶ X :=
  (FieldValuedPoint.residuePoint x).hom

/-- `fromSpecResidueField` is the morphism of the chosen residue-field point. -/
theorem fromSpecResidueField_eq {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) :
    X.fromSpecResidueField x = (FieldValuedPoint.residuePoint x).hom :=
  sorry

/-- The morphism `Spec(κ(x)) ⟶ X` is a monomorphism. -/
instance fromSpecResidueField.mono {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : Mono (X.fromSpecResidueField x) :=
  sorry

/-- The morphism `Spec(κ(x)) ⟶ X` is quasi-compact. -/
instance fromSpecResidueField.quasiCompact {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] (x : Points X) : QuasiCompact (X.fromSpecResidueField x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
