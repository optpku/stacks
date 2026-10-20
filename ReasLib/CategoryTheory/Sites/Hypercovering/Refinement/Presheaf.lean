/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Presheaf.LocallySurjective
public import ReasLib.CategoryTheory.Sites.Hypercovering.Presheaf.Augmentation
public import ReasLib.CategoryTheory.Sites.Hypercovering.Refinement
import Mathlib.Tactic.CrossRefAttribute

/-!
# Refining hypercoverings through presheaf maps

This leaf combines covering factorizations of semi-representable presheaves with degreewise
hypercovering refinement.  Local surjectivity is stated directly at the presheaf level, without
choosing a sheafification functor.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasPullbacks C] [Small.{w} C] [LocallySmall.{w} C]

namespace Hypercovering.Refinement.Presheaf

/-- Lemma 25.7.4 [stacks 01GK]: a locally surjective map onto the degree presheaf of a
hypercovering is factored by the degree map of a refining hypercovering. -/
@[stacks 01GK "refinement through a locally surjective presheaf map"]
theorem existsDegreeFactorization
    {X : C} (K : Hypercovering.{w} J X) (n : ℕ)
    {F : Cᵒᵖ ⥤ Type (max w v)} (u : F ⟶ K.degreePresheaf n)
    [Presheaf.IsLocallySurjective J u] :
    ∃ (L : Hypercovering.{w} J X) (f : L ⟶ K) (g : L.degreePresheaf n ⟶ F),
      Hypercovering.Hom.degreePresheafMap f n = g ≫ u := sorry

end Hypercovering.Refinement.Presheaf

end CategoryTheory
