/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.Refinement

/-!
# Maps in the fixed-target Cech refinement diagram

The coefficient-valued refinement diagram is owned by `Cech.Refinement` as the pullback of the
presheaf-target diagram.  This leaf exposes its morphisms with fixed-target names.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open Limits

namespace Hypercovering.Cech

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasPullbacks C]
variable [HasWeakSheafify J AddCommGrpCat.{max w v}]
variable {X : C}

/-- A homotopy-class refinement induces a natural transformation between the corresponding
Cech cohomology functors of the coefficient sheaf. -/
noncomputable abbrev refinementNatTrans
    {X : C} (i : ℕ) {K L : RefinementCategory.{w} J X} (f : K ⟶ L) :
    cohomologyInCoefficients K.unop.as i ⟶
      cohomologyInCoefficients L.unop.as i :=
  (refinementDiagram X i).map f

/-- The natural transformation associated to an identity refinement is the identity. -/
theorem refinementNatTrans_id
    (i : ℕ) (K : RefinementCategory.{w} J X) :
    refinementNatTrans i (𝟙 K) = 𝟙 _ := sorry

/-- Natural transformations associated to refinements respect composition. -/
theorem refinementNatTrans_comp
    (i : ℕ) {K L M : RefinementCategory.{w} J X}
    (f : K ⟶ L) (g : L ⟶ M) :
    refinementNatTrans i (f ≫ g) =
      refinementNatTrans i f ≫ refinementNatTrans i g := sorry

end Hypercovering.Cech

end CategoryTheory
