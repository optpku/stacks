/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Fully Faithful Functors from Bijective Hom Maps

This leaf packages a family of bijective maps on Hom sets as Mathlib's concrete
`Functor.FullyFaithful` structure.  It is independent of additive, linear, shifted, or
triangulated structure.
-/

@[expose] public section

noncomputable section

universe vC uC vD uD

namespace CategoryTheory.Functor.FullyFaithful

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

/-- A functor whose map on every Hom set is bijective has a concrete fully faithful
structure.  The inverse map is the inverse of the corresponding bundled equivalence. -/
@[stacks 09R9 "fully faithful functor from bijective Hom maps"]
noncomputable def ofMapBijective {F : C ⥤ D}
    (hF : ∀ X Y : C,
      Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y))) :
    F.FullyFaithful where
  preimage {X Y} :=
    (Equiv.ofBijective
      (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) (hF X Y)).symm
  map_preimage := sorry
  preimage_map := sorry

end CategoryTheory.Functor.FullyFaithful
