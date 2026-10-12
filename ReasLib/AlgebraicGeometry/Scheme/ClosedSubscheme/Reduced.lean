/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Structure
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reduced closed subschemes

Mathlib's `IdealSheafData.vanishingIdeal` is the canonical reduced structure
on a closed subset. This file supplies its support, radical, reducedness, and
uniqueness API, together with the reduction of a scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The support of the vanishing ideal is the closed subset from which it was constructed. -/
@[simp, stacks 01J4 "reduced induced closed subscheme"]
theorem support_vanishingIdeal (Z : TopologicalSpace.Closeds X) :
    (vanishingIdeal Z).support = Z := sorry

/-- The range of the vanishing-ideal closed-subscheme inclusion is the original closed subset. -/
@[simp, stacks 01J4 "range of reduced induced closed subscheme"]
theorem range_vanishingIdeal_subschemeι (Z : TopologicalSpace.Closeds X) :
    Set.range (vanishingIdeal Z).subschemeι = Z := sorry

/-- The closed subscheme defined by `I` is reduced exactly when `I` is radical. -/
@[stacks 01J3 "reduced closed subscheme criterion"]
theorem subscheme_isReduced_iff_radical_eq (I : X.IdealSheafData) :
    IsReduced I.subscheme ↔ I.radical = I := sorry

/-- A vanishing ideal is fixed by the radical operation. -/
@[simp, stacks 01J3 "radical of a vanishing ideal"]
theorem radical_vanishingIdeal (Z : TopologicalSpace.Closeds X) :
    (vanishingIdeal Z).radical = vanishingIdeal Z := sorry

/-- The closed subscheme defined by a vanishing ideal is reduced. -/
@[stacks 01J3 "reduced induced closed subscheme is reduced"]
instance vanishingIdeal_subscheme_isReduced (T : TopologicalSpace.Closeds X) :
    IsReduced (vanishingIdeal T).subscheme := sorry

/-- A reduced closed subscheme is the vanishing-ideal subscheme of its support. -/
@[stacks 01J3 "uniqueness of reduced induced closed subscheme"]
theorem eq_vanishingIdeal
    {T : TopologicalSpace.Closeds X} (I : X.IdealSheafData)
    [IsReduced I.subscheme] (hT : I.support = T) :
    I = vanishingIdeal T := sorry

/-- Ideal-sheaf data has support `T` and defines a reduced subscheme exactly when it is the
vanishing ideal of `T`. -/
@[stacks 01J3 "characterization of reduced induced closed subscheme"]
theorem support_eq_and_isReduced_iff
    (I : X.IdealSheafData) (T : TopologicalSpace.Closeds X) :
    I.support = T ∧ IsReduced I.subscheme ↔ I = vanishingIdeal T := sorry

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

namespace ClosedSubschemeStructure

variable {X : Scheme.{u}}

/-- The canonical reduced scheme structure on a closed subset. -/
@[stacks 01J4 "reduced induced scheme structure"]
noncomputable def reduced (Z : TopologicalSpace.Closeds X) :
    ClosedSubschemeStructure Z where
  ideal := IdealSheafData.vanishingIdeal Z
  support_eq := IdealSheafData.support_vanishingIdeal Z

/-- The defining ideal of the reduced structure is the vanishing ideal. -/
@[simp, stacks 01J4 "ideal of the reduced induced structure"]
theorem reduced_ideal (Z : TopologicalSpace.Closeds X) :
    (reduced Z).ideal = IdealSheafData.vanishingIdeal Z := sorry

/-- On the whole underlying space, the reduced structure is defined by the nilradical. -/
@[simp, stacks 01J4 "ideal of the scheme reduction"]
theorem reduced_top_ideal (X : Scheme.{u}) :
    (reduced (⊤ : TopologicalSpace.Closeds X)).ideal = X.nilradical := sorry

/-- A scheme structure on `Z` is reduced exactly when it is the canonical reduced structure. -/
@[stacks 01J3 "uniqueness of the reduced scheme structure"]
theorem isReduced_iff_eq_reduced {Z : TopologicalSpace.Closeds X}
    (T : ClosedSubschemeStructure Z) :
    IsReduced T.subscheme ↔ T = reduced Z := sorry

/-- Every closed subset has a unique reduced scheme structure. -/
@[stacks 01J3 "unique reduced scheme structure on a closed subset"]
theorem existsUnique_reduced (Z : TopologicalSpace.Closeds X) :
    ∃! T : ClosedSubschemeStructure Z, IsReduced T.subscheme := sorry

end ClosedSubschemeStructure

/-- The reduction of a scheme is its nilradical closed subscheme. -/
@[stacks 01J4 "scheme reduction"]
abbrev reduction : Scheme.{u} := X.nilradical.subscheme

/-- The canonical inclusion from the reduction into the original scheme. -/
@[stacks 01J4 "reduction inclusion"]
abbrev reductionι : reduction X ⟶ X := X.nilradical.subschemeι

/-- The reduced induced structure on the whole underlying space has the canonical reduction as
its associated scheme. -/
@[stacks 01J4 "whole-space reduced induced structure is the reduction"]
theorem ClosedSubschemeStructure.reduced_top_subscheme (X : Scheme.{u}) :
    (ClosedSubschemeStructure.reduced
      (⊤ : TopologicalSpace.Closeds X)).subscheme = reduction X := sorry

/-- Under the whole-space identification, the reduced induced inclusion is the reduction
inclusion. -/
@[stacks 01J4 "whole-space reduced induced inclusion"]
theorem ClosedSubschemeStructure.reduced_top_ι (X : Scheme.{u}) :
    eqToHom (ClosedSubschemeStructure.reduced_top_subscheme X) ≫ reductionι X =
      (ClosedSubschemeStructure.reduced (⊤ : TopologicalSpace.Closeds X)).ι := sorry

end AlgebraicGeometry.Scheme
