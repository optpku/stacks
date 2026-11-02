/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Sheafification.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of relative differentials

Restriction to the slice site over an object preserves the sheaf of relative
differentials.  The API is stated at the generic ringed-site level and uses
the canonical `over` constructions for sheaves and module sheaves.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite
open PresheafOfModules.DifferentialsConstruction

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.RelativeDifferentials

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
variable [∀ U : C,
  (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}

/-- The restriction of a commutative-ring sheaf morphism to the slice site
over `U`. -/
abbrev localizedMap (phi : O₁ ⟶ O₂) (U : C) :
    O₁.over U ⟶ O₂.over U :=
  (J.overPullback CommRingCat.{max u v} U).map phi

/-- The relative-differentials sheaf of the localized ring morphism. -/
abbrev localized (phi : O₁ ⟶ O₂) (U : C) :
    SheafOfModules (ringSheaf (J.over U) (O₂.over U)) :=
  relativeDifferentials (localizedMap phi U)

/-- The canonical module-sheaf comparison for localized differentials. -/
noncomputable def overIso (phi : O₁ ⟶ O₂) (U : C) :
    (relativeDifferentials phi).over U ≅ localized phi U :=
  ModuleSheafification.overIso O₂ U (relativeDifferentials' phi.hom)

/-- The localization comparison preserves the universal differential. -/
theorem overIso_d (phi : O₁ ⟶ O₂) (U : C) (X : (Over U)ᵒᵖ)
    (x : O₂.obj.obj (Opposite.op X.unop.left)) :
    (overIso phi U).hom.val.app X
        (((relativeDifferential phi).app (Opposite.op X.unop.left)).d x) =
      ((relativeDifferential (localizedMap phi U)).app X).d x := by
  sorry

/-- Lemma 18.33.6 (04BO): restriction of relative differentials to a slice
site is isomorphic to the relative differentials of the restricted ring
morphism. -/
@[stacks 04BO]
theorem over_isIsomorphic (phi : O₁ ⟶ O₂) (U : C) :
    IsIsomorphic
      ((SheafOfModules.toSheaf ((ringSheaf J O₂).over U)).obj
        ((relativeDifferentials phi).over U))
      ((SheafOfModules.toSheaf
        (ringSheaf (J.over U) (O₂.over U))).obj (localized phi U)) := sorry

end SheafOfModules.RingedSite.RelativeDifferentials
