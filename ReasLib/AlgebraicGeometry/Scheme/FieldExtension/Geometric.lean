/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The base change of a scheme over a field to an algebraic closure. -/
abbrev geometricBaseChange {k : Type u} [Field k] (X : SchemeOverField k) : Scheme.{u} :=
  FieldExtension.baseChange k (AlgebraicClosure k) X.hom

/-- The structure morphism from the geometric base change back to the original scheme. -/
abbrev geometricToArithmeticHom {k : Type u} [Field k] (X : SchemeOverField k) :
    geometricBaseChange X ⟶ X.left :=
  FieldExtension.toSource k (AlgebraicClosure k) X.hom

/-- Connectedness descends from the algebraic-closure base change of a scheme over a field. -/
instance connectedSpace_of_geometricBaseChange {k : Type u} [Field k]
    (X : SchemeOverField k) [ConnectedSpace (geometricBaseChange X)] :
    ConnectedSpace X.left := sorry

end AlgebraicGeometry.SchemeOverField
