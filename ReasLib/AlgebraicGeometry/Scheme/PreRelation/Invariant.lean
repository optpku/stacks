/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Invariant subobjects of a pre-relation

This module defines invariance under the source and target maps of a pre-relation.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

variable {S : Scheme.{u}} {U : Over S}

/-- A subset is invariant under a pre-relation when the target of every related point whose
source lies in the subset also lies in the subset. -/
def IsSetInvariant (P : PreRelation U) (W : Set U.left) : Prop :=
  Set.MapsTo P.t.left.base (P.s.left.base ⁻¹' W) W

/-- Set invariance expressed pointwise on the underlying points of the relation scheme. -/
theorem isSetInvariant_iff (P : PreRelation U) (W : Set U.left) :
    P.IsSetInvariant W ↔
      ∀ r : P.left.left, P.s.left.base r ∈ W → P.t.left.base r ∈ W := sorry

/-- Set invariance expressed as inclusion between the source and target preimages. -/
theorem isSetInvariant_iff_preimage_subset (P : PreRelation U) (W : Set U.left) :
    P.IsSetInvariant W ↔ P.s.left.base ⁻¹' W ⊆ P.t.left.base ⁻¹' W := sorry

/-- An open subset is invariant when its underlying set is invariant. -/
def IsOpenInvariant (P : PreRelation U) (W : U.left.Opens) : Prop :=
  P.IsSetInvariant W

/-- Open invariance is set invariance of the underlying open subset. -/
theorem isOpenInvariant_iff (P : PreRelation U) (W : U.left.Opens) :
    P.IsOpenInvariant W ↔ P.IsSetInvariant W := sorry

/-- A closed subscheme is invariant when its scheme-theoretic inverse images under the target
and source maps agree. -/
def IsClosedInvariant (P : PreRelation U) (Z : U.left.IdealSheafData) : Prop :=
  Z.comap P.t.left = Z.comap P.s.left

/-- Closed invariance expressed as equality of the two pulled-back ideal sheaves. -/
theorem isClosedInvariant_iff (P : PreRelation U) (Z : U.left.IdealSheafData) :
    P.IsClosedInvariant Z ↔ Z.comap P.t.left = Z.comap P.s.left := sorry

/-- A subobject is invariant when its pullbacks under the target and source maps agree. -/
def IsInvariant (P : PreRelation U) (Q : Subobject U.left) : Prop :=
  (Subobject.pullback P.t.left).obj Q = (Subobject.pullback P.s.left).obj Q

/-- Subobject invariance expressed as equality of the two categorical pullbacks. -/
theorem isInvariant_iff (P : PreRelation U) (Q : Subobject U.left) :
    P.IsInvariant Q ↔
      (Subobject.pullback P.t.left).obj Q = (Subobject.pullback P.s.left).obj Q := sorry

/-- Invariance of a monomorphism is invariance of the subobject represented by that
monomorphism. -/
theorem isInvariant_mk_iff {T : Scheme.{u}} (P : PreRelation U)
    (i : T ⟶ U.left) [Mono i] :
    P.IsInvariant (Subobject.mk i) ↔
      (Subobject.pullback P.t.left).obj (Subobject.mk i) =
        (Subobject.pullback P.s.left).obj (Subobject.mk i) := sorry

/-- Scheme-theoretic invariance of a closed subscheme agrees with invariance of its associated
subobject. -/
theorem isClosedInvariant_iff_isInvariant (P : PreRelation U)
    (Z : U.left.IdealSheafData) :
    P.IsClosedInvariant Z ↔ P.IsInvariant (Subobject.mk Z.subschemeι) := sorry

end AlgebraicGeometry.Scheme.PreRelation
