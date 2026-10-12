/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Absolute
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived direct image for an absolute topology comparison

For `τ' ≤ τ` on one category, the identity functor gives a direct image from `τ`-sheaves to
`τ'`-sheaves. This file owns that functor and its unbounded total right-derived functor without
introducing a slice object or a chapter dependency.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe u v

namespace CategoryTheory.GrothendieckTopology.Derived.Absolute

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}

/-- Direct image of abelian sheaves along the identity comparison `τ' ≤ τ`. -/
@[stacks 0EZF "absolute topology-comparison direct image"]
noncomputable abbrev pushforward (hle : τ' ≤ τ) :
    Sheaf τ AddCommGrpCat.{max u v} ⥤
      Sheaf τ' AddCommGrpCat.{max u v} :=
  TopologyComparison.pushforward AddCommGrpCat.{max u v} hle

/-- Absolute topology-comparison direct image is additive. -/
@[stacks 0EZF "absolute topology-comparison direct image is additive", instance]
instance pushforward_additive (hle : τ' ≤ τ) :
    (pushforward hle).Additive := sorry

/-- The quasi-isomorphism denominator for the source homotopy category. -/
@[stacks 0EZF "absolute topology-comparison denominator"]
abbrev qis (J : GrothendieckTopology C) :
    MorphismProperty
      (HomotopyCategory (Sheaf J AddCommGrpCat.{max u v}) (up ℤ)) :=
  HomotopyCategory.quasiIso (Sheaf J AddCommGrpCat.{max u v}) (up ℤ)

section Derived

variable [HasSheafify τ AddCommGrpCat.{max u v}]
variable [HasSheafify τ' AddCommGrpCat.{max u v}]

/-- The canonical unbounded right-derived direct image for `τ' ≤ τ`. -/
@[stacks 0EZF "absolute derived topology-comparison direct image"]
noncomputable abbrev rightDerived (hle : τ' ≤ τ)
    [Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived (pushforward hle)) (qis τ)] :
    DerivedCategory (Sheaf τ AddCommGrpCat.{max u v}) ⥤
      DerivedCategory (Sheaf τ' AddCommGrpCat.{max u v}) :=
  Functor.RightDerived.Homotopy.functor (pushforward hle)

/-- The unit exhibiting `rightDerived hle` as a total right-derived functor. -/
@[stacks 0EZF "absolute topology-comparison derived unit"]
noncomputable abbrev rightDerivedUnit (hle : τ' ≤ τ)
    [Functor.HasRightDerivedFunctor
      (Functor.Homotopy.toDerived (pushforward hle)) (qis τ)] :
    Functor.Homotopy.toDerived (pushforward hle) ⟶
      DerivedCategory.Qh ⋙ rightDerived hle :=
  Functor.RightDerived.Homotopy.unit (pushforward hle)

end Derived

end CategoryTheory.GrothendieckTopology.Derived.Absolute

end
