/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.ClosedFiber

/-!
# Dimensions of closed fibres under field extension

This file records dimension formulas for the closed fibre at a point of a
scheme after extending the base field.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension.Stalk.ClosedFiber

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]

/-- The Krull dimension of the closed-fibre local ring plus the transcendence degree of the
base-change residue field over the extended field equals the transcendence degree of the source
residue field over the original field. -/
theorem ringKrullDim_add_trdeg_eq
    (y : FieldExtension.baseChange k K f) :
    ringKrullDim (quotient k K f y) +
        Cardinal.toNat (Algebra.trdeg K ((FieldExtension.baseChange k K f).residueField y)) =
      Cardinal.toNat
        (Algebra.trdeg k
          (X.residueField (FieldExtension.toSource k K f y))) := sorry

/-- The Krull dimension of the closed-fibre local ring plus that of the source stalk equals the
Krull dimension of the base-change stalk. -/
theorem ringKrullDim_add_sourceStalk_eq_baseChangeStalk
    (y : FieldExtension.baseChange k K f) :
    ringKrullDim (quotient k K f y) +
        ringKrullDim (X.presheaf.stalk (FieldExtension.toSource k K f y)) =
      ringKrullDim ((FieldExtension.baseChange k K f).presheaf.stalk y) := sorry

end AlgebraicGeometry.FieldExtension.Stalk.ClosedFiber
