/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Presheaf.Cech.Ordered
import StacksCheckRecall

/-! @stack 01FI -/

@[expose] public section

open CategoryTheory Opposite TopCat.Presheaf TopologicalSpace
open TopCat.Presheaf.Cech

noncomputable section

universe u v

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]

/-!
Definition 20.23.2 (01FI) is a recall of the canonical ordered Cech complex owner.  The cover
equality from the textbook is background data for later augmentation statements; the complex
construction itself only uses the indexed family, its linear order, and the presheaf.

The root-level names below are temporary source-facing bridges for older Chapter 20 files.  New
code should use `TopCat.Presheaf.Cech.Ordered.complex` and `complexOfOrder` directly.
-/

/- Definition 20.23.2 (01FI): the ordered Cech complex owner. -/
@[stacks 01FI]
#check @TopCat.Presheaf.Cech.Ordered.complex

/-- Historical bridge for the ordered Cech complex name used by adjacent Chapter 20 entries. -/
abbrev orderedCechComplex (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :=
  TopCat.Presheaf.Cech.Ordered.complex 𝒰 F

/-- Historical bridge for an ordered Cech complex with an explicit order choice. -/
abbrev orderedCechComplexOfOrder (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :=
  TopCat.Presheaf.Cech.Ordered.complexOfOrder o 𝒰 F

/-- Coordinate bridge for the degreewise object of the ordered Cech complex. -/
theorem orderedCechComplex_X (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (orderedCechComplex 𝒰 F).X p = TopCat.Presheaf.Cech.Ordered.term 𝒰 F p := sorry

/-- Coordinate bridge for the ordered Cech differential. -/
theorem orderedCechComplex_d_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (orderedCechComplex 𝒰 F).X p)
    (σ : OrderedCechIndex ι (p + 1)) :
    (orderedCechComplex 𝒰 F).d p (p + 1) s σ =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        TopCat.Presheaf.Cech.restriction 𝒰 F σ j (s (σ.delete j)) := sorry

/-- Explicit-order degreewise bridge for the source-facing compatibility layer. -/
theorem orderedCechComplexOfOrder_X (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (orderedCechComplexOfOrder o 𝒰 F).X p =
      AddCommGrpCat.of ((σ : @OrderedCechIndex ι o p) →
        F.obj (op (TopCat.Presheaf.Cech.intersection 𝒰 σ))) := sorry

/-- Explicit-order differential bridge for the source-facing compatibility layer. -/
theorem orderedCechComplexOfOrder_d_apply (o : LinearOrder ι) (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (orderedCechComplexOfOrder o 𝒰 F).X p)
    (σ : @OrderedCechIndex ι o (p + 1)) :
    (orderedCechComplexOfOrder o 𝒰 F).d p (p + 1) s σ =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        TopCat.Presheaf.Cech.restriction 𝒰 F σ j (s (σ.delete j)) := sorry

#check @TopCat.Presheaf.Cech.Ordered.complex
#check @TopCat.Presheaf.Cech.Ordered.complexOfOrder
#check @TopCat.Presheaf.Cech.Ordered.complex_d_apply
#check @TopCat.Presheaf.Cech.Ordered.complexOfOrder_d_apply

end

end
