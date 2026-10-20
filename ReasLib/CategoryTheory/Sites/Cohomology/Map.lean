/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps on site cohomology

For abelian sheaves on a site, the objectwise morphism on the cohomology presheaf
is evaluated at an explicit site object. This also specializes to global cohomology
by evaluation at a terminal object.
-/

@[expose] public section

open CategoryTheory
open Opposite

noncomputable section

universe z w u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasExt.{z} (Sheaf J AddCommGrpCat.{w})]

/-- The morphism on degree-`i` cohomology over a site object `U` induced by a morphism
`φ : F ⟶ G` of abelian sheaves. -/
@[stacks 01FA "objectwise cohomology map"]
noncomputable abbrev cohomologyMap
    {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G) (i : ℕ) (U : C) :
    F.H' i U ⟶ G.H' i U :=
  ((cohomologyPresheafFunctor J i).map φ).app (op U)

/-- The defining cohomology-presheaf component for `cohomologyMap`. -/
theorem cohomologyMap_def
    {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G) (i : ℕ) (U : C) :
    cohomologyMap φ i U = ((cohomologyPresheafFunctor J i).map φ).app (op U) := sorry

/-- The cohomology map induced by an identity morphism is the identity at every site object. -/
@[simp]
theorem cohomologyMap_id
    (F : Sheaf J AddCommGrpCat.{w}) (i : ℕ) (U : C) :
    cohomologyMap (𝟙 F) i U = 𝟙 _ := sorry

/-- Cohomology maps respect composition of sheaf morphisms. -/
theorem cohomologyMap_comp
    {F G K : Sheaf J AddCommGrpCat.{w}}
    (φ : F ⟶ G) (ψ : G ⟶ K) (i : ℕ) (U : C) :
    cohomologyMap (φ ≫ ψ) i U = cohomologyMap φ i U ≫ cohomologyMap ψ i U := sorry

end CategoryTheory.Sheaf
