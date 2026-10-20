/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coreflective full subcategories from lifted equivalences

An adjunction whose left adjoint factors through an object-property full subcategory induces a
coreflection onto that subcategory whenever the lifted functor is an equivalence.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory.ObjectProperty.FullSubcategory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {P : ObjectProperty D} {F : C ⥤ D} {G : D ⥤ C}

/-- If the left adjoint in `F ⊣ G` lifts to an equivalence with the full subcategory cut out by
`P`, then the full-subcategory inclusion is left adjoint to `G` followed by that lift. -/
@[stacks 0AEF "full-subcategory coreflection from an equivalence lift"]
noncomputable def inclusionAdjunctionOfLift
    (adj : F ⊣ G) (hF : ∀ X, P (F.obj X))
    [(P.lift F hF).IsEquivalence] :
    P.ι ⊣ G ⋙ P.lift F hF :=
  ((P.lift F hF).asEquivalence.symm.toAdjunction.comp adj).ofNatIsoLeft
    (Iso.inverseCompIso (P.liftCompιIso F hF).symm)

end CategoryTheory.ObjectProperty.FullSubcategory
