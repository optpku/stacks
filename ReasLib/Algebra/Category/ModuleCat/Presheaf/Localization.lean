/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.CategoryTheory.Functor.Over.LeftKanExtension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of presheaves of modules

For a ring presheaf `R` on `C` and `U : C`, this file names the adjunctions around restriction to
the slice `C / U`.  It also exposes the canonical map from the coproduct indexed by arrows
`V ⟶ U` to the value at `V` of lower shriek.  The coproduct formula is stated as invertibility
of that explicit map, so no inverse data is manufactured from deferred proof obligations.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u

namespace PresheafOfModules.Localization

variable {C : Type u} [SmallCategory C]
variable (R : Cᵒᵖ ⥤ RingCat.{u}) (U : C)

/-- Restriction of module presheaves to the slice over `U`. -/
@[stacks 03EJ "presheaf restriction"]
noncomputable abbrev restriction :
    PresheafOfModules R ⥤ PresheafOfModules ((Over.forget U).op ⋙ R) :=
  PresheafOfModules.pushforward (𝟙 ((Over.forget U).op ⋙ R))

/-- Presheaf lower shriek from the slice over `U`, defined as the canonical left adjoint of
restriction. -/
@[stacks 03EJ "presheaf lower shriek"]
noncomputable abbrev lowerShriek :
    PresheafOfModules ((Over.forget U).op ⋙ R) ⥤ PresheafOfModules R :=
  PresheafOfModules.pullback (𝟙 ((Over.forget U).op ⋙ R))

/-- Presheaf lower shriek is left adjoint to restriction to the slice. -/
@[stacks 03EJ "presheaf lower-shriek adjunction"]
noncomputable def lowerShriekRestrictionAdj :
    lowerShriek R U ⊣ restriction R U :=
  PresheafOfModules.pullbackPushforwardAdjunction
    (𝟙 ((Over.forget U).op ⋙ R))

/-- The component indexed by `φ : V ⟶ U` of the canonical coproduct map into the value at
`V` of presheaf lower shriek. -/
@[stacks 03EJ "presheaf lower-shriek summand map"]
noncomputable def summandToLowerShriek
    (G : PresheafOfModules ((Over.forget U).op ⋙ R))
    (V : C) (φ : V ⟶ U) :
    G.obj (op (Over.mk φ)) ⟶ ((lowerShriek R U).obj G).obj (op V) :=
  ((lowerShriekRestrictionAdj R U).unit.app G).app (op (Over.mk φ))

/-- The canonical map from the direct sum over arrows `V ⟶ U` to the value at `V` of
presheaf lower shriek. -/
@[stacks 03EJ "presheaf lower-shriek coproduct map"]
noncomputable def coproductToLowerShriek
    (G : PresheafOfModules ((Over.forget U).op ⋙ R)) (V : C) :
    (∐ fun φ : V ⟶ U ↦ G.obj (op (Over.mk φ))) ⟶
      ((lowerShriek R U).obj G).obj (op V) :=
  Sigma.desc (summandToLowerShriek R U G V)

/-- The canonical coproduct map computes presheaf lower shriek objectwise. -/
@[stacks 03EJ "presheaf lower-shriek coproduct formula"]
theorem coproductToLowerShriek_isIso
    (G : PresheafOfModules ((Over.forget U).op ⋙ R)) (V : C) :
    IsIso (coproductToLowerShriek R U G V) := sorry

/-- Restriction of module presheaves to the slice has a right adjoint.  This is a
named instance so downstream code can use the canonical `Functor.rightAdjoint` without rebuilding
local adjunction state. -/
@[stacks 03EJ "presheaf direct image exists"]
noncomputable instance restrictionIsLeftAdjoint :
    Functor.IsLeftAdjoint (restriction R U) := sorry

section DirectImage

variable [(restriction R U).IsLeftAdjoint]

/-- Presheaf direct image from the slice over `U`, defined at the abstract adjunction layer so a
concrete right-adjoint construction can be supplied independently. -/
@[stacks 03EJ "presheaf direct image"]
noncomputable abbrev directImage :
    PresheafOfModules ((Over.forget U).op ⋙ R) ⥤ PresheafOfModules R :=
  (restriction R U).rightAdjoint

/-- Restriction of module presheaves to the slice is left adjoint to presheaf direct image. -/
@[stacks 03EJ "presheaf restriction-direct image adjunction"]
noncomputable def restrictionDirectImageAdj :
    restriction R U ⊣ directImage R U :=
  Adjunction.ofIsLeftAdjoint (restriction R U)

/-- The Hom equivalence characterizing presheaf direct image as the right adjoint of
restriction. -/
@[stacks 03EJ "presheaf restriction-direct image Hom equivalence"]
noncomputable def restrictionDirectImageHomEquiv
    (F : PresheafOfModules R)
    (G : PresheafOfModules ((Over.forget U).op ⋙ R)) :
    ((restriction R U).obj F ⟶ G) ≃ (F ⟶ (directImage R U).obj G) :=
  (restrictionDirectImageAdj R U).homEquiv F G

end DirectImage

/-- Presheaf lower shriek along slice localization is exact. -/
@[stacks 03EJ "presheaf lower shriek is exact"]
theorem lowerShriek_exact :
    exactFunctor _ _ (lowerShriek R U) := sorry

end PresheafOfModules.Localization
