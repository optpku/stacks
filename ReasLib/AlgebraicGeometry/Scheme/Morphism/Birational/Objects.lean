/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Isomorphism of Function Fields and Generic-Point Schemes

This leaf defines isomorphism of function fields and of generic-point schemes over a base.
Birationality itself is `Scheme.Birational` / `Scheme.BirationalOver` in mathlib (Stacks 0A20).
These predicates are distinct from birationality in general; the relative criterion under
local finite presentation (Stacks 0BAD) is stated in `Birational.GenericPointStalk`.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- The rings of rational functions of two irreducible schemes are isomorphic.
Without reducedness these rings need not be fields. This does not define birationality. -/
def HasIsomorphicFunctionFields (X Y : Scheme) [IrreducibleSpace X]
    [IrreducibleSpace Y] : Prop :=
  CategoryTheory.IsIsomorphic X.functionField Y.functionField

/-- Isomorphism of rings of rational functions is symmetric. -/
theorem HasIsomorphicFunctionFields.symm {X Y : Scheme} [IrreducibleSpace X]
    [IrreducibleSpace Y] :
    HasIsomorphicFunctionFields X Y → HasIsomorphicFunctionFields Y X := by
  rintro ⟨e⟩
  exact ⟨e.symm⟩

/-- Isomorphism of rings of rational functions is a symmetric relation. -/
theorem hasIsomorphicFunctionFields_comm (X Y : Scheme) [IrreducibleSpace X]
    [IrreducibleSpace Y] :
    HasIsomorphicFunctionFields X Y ↔ HasIsomorphicFunctionFields Y X :=
  ⟨HasIsomorphicFunctionFields.symm, HasIsomorphicFunctionFields.symm⟩

/-- The generic-point scheme of an irreducible scheme over `S`, regarded as an
object of the over category of `S`. -/
noncomputable abbrev genericPointOver
    (S X : Scheme) [X.Over S] [IrreducibleSpace X] : Over S :=
  Over.mk (X.fromSpecStalk (genericPoint X) ≫ (X ↘ S))

/-- The generic-point schemes of two irreducible schemes are isomorphic in `Over S`.
The bridge to `Scheme.BirationalOver` under local finite presentation is
`Scheme.birationalOver_tfae_of_locallyOfFinitePresentation`. -/
def HasIsomorphicGenericPointsOver (S X Y : Scheme) [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y] : Prop :=
  CategoryTheory.IsIsomorphic (genericPointOver S X) (genericPointOver S Y)

/-- Isomorphism of generic-point schemes over a base is symmetric. -/
theorem HasIsomorphicGenericPointsOver.symm {S X Y : Scheme} [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    HasIsomorphicGenericPointsOver S X Y → HasIsomorphicGenericPointsOver S Y X := by
  rintro ⟨e⟩
  exact ⟨e.symm⟩

/-- Isomorphism of generic-point schemes over a base is a symmetric relation. -/
theorem hasIsomorphicGenericPointsOver_comm (S X Y : Scheme) [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    HasIsomorphicGenericPointsOver S X Y ↔ HasIsomorphicGenericPointsOver S Y X :=
  ⟨HasIsomorphicGenericPointsOver.symm, HasIsomorphicGenericPointsOver.symm⟩

end AlgebraicGeometry
