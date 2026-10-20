/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Property (β) for algebraic spaces

An algebraic space has property (β) when each point is represented by a monomorphism
from the spectrum of a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space has property (β) if every point is represented by a monomorphism from
the spectrum of a field. -/
@[mk_iff]
class HasPropertyBeta {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- Every point arises from a monomorphism `Spec(K) ⟶ X`. -/
  exists_mono :
    ∀ x : Points X, ∃ p : FieldValuedPoint X, Mono p.hom ∧ Points.mk p = x

namespace HasPropertyBeta

/-- An algebraic space with property (β) has, at every point, a monomorphism from the spectrum
of a field representing that point. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [HasPropertyBeta X] :
    ∀ x : Points X, ∃ p : FieldValuedPoint X, Mono p.hom ∧ Points.mk p = x :=
  sorry

/-- A choice of monomorphism `Spec(K) ⟶ X` at every point witnesses property (β). -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ x : Points X, ∃ p : FieldValuedPoint X, Mono p.hom ∧ Points.mk p = x) :
    HasPropertyBeta X :=
  sorry

end HasPropertyBeta

/-- A scheme over `S`, viewed as an algebraic space, has property (β). -/
instance instHasPropertyBeta_ofOver {S : Scheme.{u}} (T : Over S) :
    HasPropertyBeta (ofOver T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
