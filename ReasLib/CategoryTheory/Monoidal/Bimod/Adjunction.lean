/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
public import ReasLib.CategoryTheory.Monoidal.Bimod.ChangeOfScalars
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module categories induced by a monoidal adjunction

A monoidal right adjoint transports modules over a monoid object.  When the adjunction satisfies
the projection formula, its left adjoint transports those modules back: the target action is the
projection-formula isomorphism followed by the image of the source action.  This file constructs
that left adjoint explicitly and lifts the ambient adjunction to right-module categories.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory

noncomputable section

universe uC vC uD vD

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
variable [R.LaxMonoidal] [L.OplaxMonoidal] [adj.IsMonoidal]
variable [adj.ProjectionFormulaMap]

namespace RightModuleLowerShriek

variable (A : Mon D)

/-- The right action on the lower shriek of an `R(A)`-module. -/
@[stacks 0FRA "projection-formula action on module lower shriek"]
noncomputable def actRight (M : Bimod.RightModule (R.mapMon.obj A)) :
    L.obj M.X ⊗ A.X ⟶ L.obj M.X :=
  (adj.projectionFormulaMapIso M.X A.X).hom ≫ L.map M.actRight

/-- The lower shriek of a right `R(A)`-module as an explicit right `A`-module. -/
@[stacks 0FRA "right-module lower shriek object"]
noncomputable def obj (M : Bimod.RightModule (R.mapMon.obj A)) :
    Bimod.RightModule A where
  X := L.obj M.X
  actLeft := (λ_ (L.obj M.X)).hom
  actRight := actRight adj A M
  one_actLeft := sorry
  left_assoc := sorry
  actRight_one := sorry
  right_assoc := sorry
  middle_assoc := sorry

/-- The carrier of a lower-shrieked right module is the ambient left-adjoint image. -/
@[simp]
theorem obj_X (M : Bimod.RightModule (R.mapMon.obj A)) :
    (obj adj A M).X = L.obj M.X := sorry

/-- The right action on a lower-shrieked module is induced by the projection formula. -/
@[simp]
theorem obj_actRight (M : Bimod.RightModule (R.mapMon.obj A)) :
    (obj adj A M).actRight =
      (adj.projectionFormulaMapIso M.X A.X).hom ≫ L.map M.actRight := sorry

/-- Applying the ambient left adjoint to a module morphism gives a morphism between module
lower shrieks. -/
noncomputable def map {M N : Bimod.RightModule (R.mapMon.obj A)} (f : M ⟶ N) :
    obj adj A M ⟶ obj adj A N where
  hom := L.map f.hom
  left_act_hom := sorry
  right_act_hom := sorry

/-- The carrier map of a lower-shrieked module morphism is the ambient functorial image. -/
@[simp]
theorem map_hom {M N : Bimod.RightModule (R.mapMon.obj A)} (f : M ⟶ N) :
    (map adj A f).hom = L.map f.hom := sorry

/-- Module lower shriek preserves identity morphisms. -/
theorem map_id (M : Bimod.RightModule (R.mapMon.obj A)) :
    map adj A (𝟙 M) = 𝟙 (obj adj A M) := sorry

/-- Module lower shriek preserves composition of morphisms. -/
theorem map_comp {M N P : Bimod.RightModule (R.mapMon.obj A)}
    (f : M ⟶ N) (g : N ⟶ P) :
    map adj A (f ≫ g) = map adj A f ≫ map adj A g := sorry

end RightModuleLowerShriek

/-- The left adjoint induced on right-module categories by a monoidal adjunction satisfying the
projection formula. -/
@[stacks 0FRA "right-module lower shriek functor"]
noncomputable def rightModuleLowerShriek (A : Mon D) :
    Bimod.RightModule (R.mapMon.obj A) ⥤ Bimod.RightModule A where
  obj := RightModuleLowerShriek.obj adj A
  map := RightModuleLowerShriek.map adj A
  map_id := RightModuleLowerShriek.map_id adj A
  map_comp := RightModuleLowerShriek.map_comp adj A

/-- The underlying object of module lower shriek is the ambient left-adjoint image. -/
@[simp]
theorem rightModuleLowerShriek_obj_X (A : Mon D)
    (M : Bimod.RightModule (R.mapMon.obj A)) :
    ((adj.rightModuleLowerShriek A).obj M).X = L.obj M.X := sorry

/-- Transpose a right-module morphism across the ambient monoidal adjunction. -/
noncomputable def rightModuleHomForward (A : Mon D)
    (M : Bimod.RightModule (R.mapMon.obj A)) (N : Bimod.RightModule A)
    (f : (adj.rightModuleLowerShriek A).obj M ⟶ N) :
    M ⟶ (R.mapRightModule A).obj N where
  hom := adj.homEquiv M.X N.X f.hom
  left_act_hom := sorry
  right_act_hom := sorry

/-- Transpose a right-module morphism backwards across the ambient monoidal adjunction. -/
noncomputable def rightModuleHomBackward (A : Mon D)
    (M : Bimod.RightModule (R.mapMon.obj A)) (N : Bimod.RightModule A)
    (f : M ⟶ (R.mapRightModule A).obj N) :
    (adj.rightModuleLowerShriek A).obj M ⟶ N where
  hom := (adj.homEquiv M.X N.X).symm f.hom
  left_act_hom := sorry
  right_act_hom := sorry

/-- The module-level Hom equivalence induced by an ambient monoidal adjunction satisfying the
projection formula. -/
@[stacks 0FRA "right-module lower-shriek Hom equivalence"]
noncomputable def rightModuleHomEquiv (A : Mon D)
    (M : Bimod.RightModule (R.mapMon.obj A)) (N : Bimod.RightModule A) :
    ((adj.rightModuleLowerShriek A).obj M ⟶ N) ≃
      (M ⟶ (R.mapRightModule A).obj N) where
  toFun := rightModuleHomForward adj A M N
  invFun := rightModuleHomBackward adj A M N
  left_inv := sorry
  right_inv := sorry

/-- The natural Hom equivalences defining the lifted right-module adjunction. -/
noncomputable def rightModuleCoreHomEquiv (A : Mon D) :
    CoreHomEquiv (adj.rightModuleLowerShriek A) (R.mapRightModule A) where
  homEquiv := adj.rightModuleHomEquiv A
  homEquiv_naturality_left_symm := sorry
  homEquiv_naturality_right := sorry

/-- Lemma 24.10.1 (0FRA), generic form: a monoidal adjunction satisfying the projection formula
lifts to an adjunction between right-module categories. -/
@[stacks 0FRA "right-module lower-shriek adjunction"]
noncomputable def rightModuleAdjunction (A : Mon D) :
    adj.rightModuleLowerShriek A ⊣ R.mapRightModule A :=
  Adjunction.mkOfHomEquiv (adj.rightModuleCoreHomEquiv A)

/-- The Hom equivalence of the lifted module adjunction is the explicit module transpose. -/
theorem rightModuleAdjunction_homEquiv (A : Mon D)
    (M : Bimod.RightModule (R.mapMon.obj A)) (N : Bimod.RightModule A) :
    (adj.rightModuleAdjunction A).homEquiv M N = adj.rightModuleHomEquiv A M N := sorry

/-- Monoidal transport of right modules is canonically a right adjoint when the canonical ambient
left adjoint satisfies the projection formula.  Formulating the instance through
`R.IsRightAdjoint` makes every input recoverable from the target functor. -/
@[stacks 0FRA "right-module restriction is a right adjoint"]
noncomputable instance mapRightModule_isRightAdjoint
    {R : D ⥤ C} [R.IsRightAdjoint] [R.LaxMonoidal]
    [(R.leftAdjoint).OplaxMonoidal]
    [(Adjunction.ofIsRightAdjoint R).IsMonoidal]
    [(Adjunction.ofIsRightAdjoint R).ProjectionFormulaMap]
    (A : Mon D) :
    (R.mapRightModule A).IsRightAdjoint :=
  ((Adjunction.ofIsRightAdjoint R).rightModuleAdjunction A).isRightAdjoint

end CategoryTheory.Adjunction

end
