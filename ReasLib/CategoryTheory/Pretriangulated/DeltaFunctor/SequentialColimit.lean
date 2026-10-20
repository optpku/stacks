/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.Sequential
public import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Definition
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Construction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential colimits under delta functors

An additive delta functor which preserves the relevant countable coproduct sends an exact
sequential colimit in its abelian source to a homotopy colimit in its pretriangulated target.
The telescope map, boundary, distinguished triangle, and presentation are exposed separately.
-/

@[expose] public section

noncomputable section

universe vA uA vD uD

open CategoryTheory.Limits
open CategoryTheory.Limits.Sequential
open CategoryTheory.Pretriangulated

namespace CategoryTheory.DeltaFunctor.SequentialColimit

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ]
variable [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable [HasColimitsOfShape ℕ A]
variable [HasExactColimitsOfShape ℕ A]
variable [HasCoproductsOfShape ℕ A] [HasCoproductsOfShape ℕ D]

variable (F : DeltaFunctor A D) (S : ℕ ⥤ A)
variable [PreservesColimit (Discrete.functor S.obj) F.toFunctor]

/-- The canonical map from the coproduct of the images to the image of the sequential
colimit. -/
noncomputable def toCocone :
    ∐ (S ⋙ F.toFunctor).obj ⟶ F.obj (colimit S) :=
  (PreservesCoproduct.iso F.toFunctor S.obj).inv ≫
    F.map (Limits.Sigma.desc (colimit.ι S))

/-- The connecting morphism of the telescope triangle obtained from the short exact telescope
sequence in the source. -/
noncomputable def connecting :
    F.obj (colimit S) ⟶ (∐ (S ⋙ F.toFunctor).obj)⟦(1 : ℤ)⟧ :=
  F.δ (S := telescopeShortComplex S) (telescopeMap_shortExact S) ≫
    ((PreservesCoproduct.iso F.toFunctor S.obj).hom⟦(1 : ℤ)⟧')

/-- The telescope triangle associated to an exact sequential colimit under a delta functor. -/
noncomputable def triangle : Triangle D :=
  Triangle.mk (telescopeMap (S ⋙ F.toFunctor)) (toCocone F S) (connecting F S)

/-- The telescope triangle associated to an exact sequential colimit is distinguished. -/
theorem distinguished :
    Triangle.mk (telescopeMap (S ⋙ F.toFunctor))
      (toCocone F S) (connecting F S) ∈ distTriang D := sorry

/-- The canonical telescope presentation of the image of an exact sequential colimit. -/
@[stacks 0FTC "delta functors preserve sequential colimits as homotopy colimits"]
noncomputable def presentation :
    HomotopyColimit.Presentation (S ⋙ F.toFunctor) (F.obj (colimit S)) :=
  HomotopyColimit.Presentation.ofCoproductTriangle
    (toCocone F S) (connecting F S) (distinguished F S)

/-- The `n`th leg of the canonical presentation is the image of the termwise colimit map. -/
@[simp]
theorem presentation.ι (n : ℕ) :
    (presentation F S).ι n = F.map (colimit.ι S n) := sorry

/-- Lemma 24.27.2 (0FTC): an exact sequential colimit is sent by a coproduct-preserving delta
functor to a homotopy colimit. -/
@[stacks 0FTC "exact sequential colimits under a delta functor"]
theorem isOf :
    HomotopyColimit.IsOf (S ⋙ F.toFunctor) (F.obj (colimit S)) := sorry

end CategoryTheory.DeltaFunctor.SequentialColimit
