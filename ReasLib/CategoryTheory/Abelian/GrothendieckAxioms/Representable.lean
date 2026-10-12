/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import ReasLib.CategoryTheory.Adjunction.Representability
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Representable presheaves on Grothendieck abelian categories

For a `Type`-valued presheaf on a Grothendieck abelian category, preservation of
limits is equivalent to representability.
-/

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.IsGrothendieckAbelian.Representable

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]

/-- A limit-preserving `Type`-valued presheaf on a Grothendieck abelian category is a
right adjoint. -/
@[stacks 07D7 "right adjoint criterion"]
theorem rightAdjoint_of_preservesLimits (F : Aᵒᵖ ⥤ Type v)
    [PreservesLimits F] : F.IsRightAdjoint := sorry

/-- Lemma 19.13.1: a `Type`-valued presheaf on a Grothendieck abelian category is
representable if and only if it preserves limits. -/
@[stacks 07D7]
theorem iff_preservesLimits (F : Aᵒᵖ ⥤ Type v) :
    F.IsRepresentable ↔ PreservesLimits F := sorry

end CategoryTheory.IsGrothendieckAbelian.Representable
