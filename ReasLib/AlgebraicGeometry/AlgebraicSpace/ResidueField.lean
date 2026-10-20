/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Monomorphism

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
  (IsDecent.exists_quasiCompact_mono x).choose_spec

/-- The chosen residue-field point represents `x`. -/
theorem mk_residuePoint {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) : Points.mk (residuePoint x) = x :=
  (residuePoint_spec x).2.2

/-- Any field-valued point representing `x` factors uniquely through the residue-field
point. -/
theorem unique_factorization_residuePoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {x : Points X} (p : FieldValuedPoint X) (hp : Points.mk p = x) :
    Nonempty (p.Factorization (residuePoint x)) ∧
      Subsingleton (p.Factorization (residuePoint x)) :=
  unique_factorization_of_mono (residuePoint_spec x).2.1
    (hp.trans (mk_residuePoint x).symm)

/-- On a scheme over `S`, the algebraic-space residue-field point is equivalent to the
scheme residue-field point. -/
theorem residuePoint_ofOver {S : Scheme.{u}} (T : Over S) (t : T.left) :
    Equivalent (residuePoint (ofOver.pointsEquiv T t))
      (ofScheme (Scheme.FieldValuedPoint.residuePoint t)) :=
  (Points.mk_eq_mk_iff _ _).mp
    ((mk_residuePoint _).trans (ofOver.pointsEquiv_apply T t))

end FieldValuedPoint

/-- The residue field of a decent algebraic space `X` at a point `x`. -/
abbrev residueField {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X) :
    CommRingCat :=
  .of (FieldValuedPoint.residuePoint x).K

/-- The residue field is the source field of the chosen residue-field point. -/
theorem residueField_eq {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) :
    X.residueField x = .of (FieldValuedPoint.residuePoint x).K :=
  rfl

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
  rfl

/-- The morphism `Spec(κ(x)) ⟶ X` is a monomorphism. -/
instance fromSpecResidueField.mono {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    (x : Points X) : Mono (X.fromSpecResidueField x) :=
  (FieldValuedPoint.residuePoint_spec x).2.1

/-- The morphism `Spec(κ(x)) ⟶ X` is quasi-compact. -/
instance fromSpecResidueField.quasiCompact {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] (x : Points X) : QuasiCompact (X.fromSpecResidueField x) :=
  (FieldValuedPoint.residuePoint_spec x).1

open FieldValuedPoint

/-- The composite `Spec(κ(x)) ⟶ Y` factors through `Spec(κ(Points.map f x)) ⟶ Y`. -/
theorem exists_residuePointFactor {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) :
    Nonempty (Factorization ((residuePoint x).map f)
      (residuePoint (Points.map f x))) :=
  (unique_factorization_residuePoint ((residuePoint x).map f)
    ((Points.map_mk f (residuePoint x)).symm.trans
      (congrArg (Points.map f) (mk_residuePoint x)))).1

/-- A factorization of `Spec(κ(x)) ⟶ Y` through `Spec(κ(Points.map f x)) ⟶ Y` is
unique. -/
theorem subsingleton_residuePointFactor {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X) :
    Subsingleton (Factorization ((residuePoint x).map f)
      (residuePoint (Points.map f x))) :=
  (unique_factorization_residuePoint ((residuePoint x).map f)
    ((Points.map_mk f (residuePoint x)).symm.trans
      (congrArg (Points.map f) (mk_residuePoint x)))).2

/-- A morphism `f : X ⟶ Y` of decent algebraic spaces induces an isomorphism
`κ(Points.map f x) ⟶ κ(x)` if and only if the composite `Spec(κ(x)) ⟶ Y` is a
monomorphism. The induced field homomorphism is represented by the source-spectrum
map of a factorization of `(residuePoint x).map f` through
`residuePoint (Points.map f x)`. -/
theorem identifiesResidueFields_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) (x : Points X)
    (φ : Factorization ((residuePoint x).map f) (residuePoint (Points.map f x))) :
    IsIso φ.schemeHom ↔ Mono (X.fromSpecResidueField x ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
