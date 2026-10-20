/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Functor.TensorComparison
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Braiding reversal for tensor comparisons

@stack 08I3

A tensor comparison may be transported through the reverse braidings on its source and target.
This leaf records that construction without requiring the functor itself to preserve braidings.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe uC vC uD vD uE vE

namespace CategoryTheory.Functor.TensorComparison

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D] [BraidedCategory D]

/-- 08I3: The reverse braiding as an isomorphism from tensor to factor-swapped tensor. -/
@[stacks 08I3 "reverse braiding tensor comparison"]
noncomputable def reverseBraidingNatIso
    (C : Type uC) [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C] :
    tensorFunctor C ≅ CategoryTheory.Prod.swap C C ⋙ tensorFunctor C :=
  NatIso.ofComponents
    (fun X ↦ (β_ X.2 X.1).symm)
    (by
      intro X Y f
      rcases X with ⟨X₁, X₂⟩
      rcases Y with ⟨Y₁, Y₂⟩
      rcases f with ⟨f₁, f₂⟩
      exact BraidedCategory.braiding_inv_naturality f₁ f₂)

/-- 08I3: Conjugate a tensor comparison by the reverse braidings on source and target. -/
@[stacks 08I3 "braiding-reversed tensor comparison"]
noncomputable def reverse (F : C ⥤ D) (T : TensorComparison F) : TensorComparison F :=
  Functor.isoWhiskerRight (reverseBraidingNatIso C) F ≪≫
    Functor.isoWhiskerLeft (CategoryTheory.Prod.swap C C) T ≪≫
    Functor.isoWhiskerLeft (Functor.prod F F) (reverseBraidingNatIso D).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 08I3: Reversing tensor comparisons commutes with composition of functors. -/
@[stacks 08I3 "composition of braiding-reversed tensor comparisons"]
theorem reverse_comp
    {E : Type uE} [Category.{vE} E] [MonoidalCategory E] [BraidedCategory E]
    (F : C ⥤ D) (G : D ⥤ E)
    (T : TensorComparison F) (U : TensorComparison G) :
    reverse (F ⋙ G) (comp F G T U) =
      comp F G (reverse F T) (reverse G U) := by
  ext X
  rcases X with ⟨X₁, X₂⟩
  simp [reverse, reverseBraidingNatIso, comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- 08I3: Reversing the identity tensor comparison leaves it unchanged. -/
@[stacks 08I3 "identity braiding-reversed tensor comparison"]
theorem reverse_id
    (C : Type uC) [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C] :
    reverse (𝟭 C) (id C) = id C := by
  ext X
  rcases X with ⟨X₁, X₂⟩
  simp [reverse, reverseBraidingNatIso, id]

end CategoryTheory.Functor.TensorComparison
