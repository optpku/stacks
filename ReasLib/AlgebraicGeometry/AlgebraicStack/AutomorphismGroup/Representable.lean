/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable

/-!
# Algebraic-space representability of automorphism groups

The automorphism group object of a field-valued point of an algebraic stack
is representable by an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.automorphismGroup

/-- The automorphism group object of a field-valued point of an algebraic stack
is representable by an algebraic space. -/
theorem isRepresentableByAlgebraicSpace {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (p : FieldValuedPoint X) :
    IsRepresentableByAlgebraicSpace (automorphismGroup p) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.automorphismGroup
