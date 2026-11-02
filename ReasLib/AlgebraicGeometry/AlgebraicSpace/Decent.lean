/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Decent algebraic spaces

An algebraic space is decent when every point is represented by a quasi-compact
monomorphism from the spectrum of a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is decent if every point is represented by a quasi-compact
monomorphism from the spectrum of a field. -/
@[mk_iff]
class IsDecent {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- Every point arises from a quasi-compact monomorphism `Spec(K) ⟶ X`. -/
  exists_quasiCompact_mono :
    ∀ x : Points X, ∃ p : FieldValuedPoint X,
      QuasiCompact p.hom ∧ Mono p.hom ∧ Points.mk p = x

namespace IsDecent

/-- A decent algebraic space has, at every point, a quasi-compact monomorphism from
the spectrum of a field representing that point. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] :
    ∀ x : Points X, ∃ p : FieldValuedPoint X,
      QuasiCompact p.hom ∧ Mono p.hom ∧ Points.mk p = x :=
  IsDecent.exists_quasiCompact_mono

/-- A choice of quasi-compact monomorphism `Spec(K) ⟶ X` at every point witnesses
that the algebraic space is decent. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ x : Points X, ∃ p : FieldValuedPoint X,
      QuasiCompact p.hom ∧ Mono p.hom ∧ Points.mk p = x) :
    IsDecent X := ⟨h⟩

end IsDecent

/-- A scheme over `S`, viewed as an algebraic space, is decent. -/
instance instIsDecent_ofOver {S : Scheme.{u}} (T : Over S) : IsDecent (ofOver T) :=
  sorry

/-- A quasi-separated algebraic space is decent. -/
instance instIsDecent_of_isQuasiSeparated {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiSeparated X] : IsDecent X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
