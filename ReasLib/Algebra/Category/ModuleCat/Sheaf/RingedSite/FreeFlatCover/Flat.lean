/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Colimits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FreeFlatCover.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness of the canonical free cover

The summands `j_{U!} O_U` are flat, hence so is their coproduct. This leaf packages the
functorial free cover as a `FlatPresentation` and installs the resulting enough-flat-objects
instance. As in `FreeFlatCover.Construction`, the common universe is `max u v w`; existence of
the localization left adjoints is exposed as the precise reusable hypothesis.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.FreeFlatCover

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ RingCat.{max u v w} AddCommGrpCat.{max u v w})]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
variable {O : Sheaf J CommRingCat.{max u v w}}
variable [SheafOfModules.Localization.HasLowerShriek.{max u v w} (ringSheaf J O)]

/-- Every localized structure-module summand in the canonical cover is flat. -/
theorem summand_isFlat
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O)
    (i : Index M) :
    MonoidalCategory.IsFlat (summand M i) := sorry

/-- The canonical free object is flat. -/
@[stacks 01DQ "canonical flat replacement", instance]
theorem obj_isFlat
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :
    MonoidalCategory.IsFlat (obj M) := sorry

/-- The canonical coproduct and its evaluation map give a flat presentation of `M`. -/
@[stacks 01DQ "canonical flat presentation"]
noncomputable def presentation
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :
    FlatPresentation M where
  source := obj M
  isFlat := obj_isFlat M
  map := πApp M
  epi_map := epi_πApp M

/-- The source of the canonical flat presentation is the canonical free flat object. -/
@[simp]
theorem presentation_source
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :
    (presentation M).source = obj M := sorry

/-- The map of the canonical flat presentation is the canonical free flat cover. -/
@[simp]
theorem presentation_map
    (M : ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) :
    (presentation M).map = πApp M := sorry

/-- Module sheaves on a ringed site have enough flat objects. -/
@[stacks 01DQ "enough flat module sheaves"]
noncomputable instance enoughFlatObjects
    (O : Sheaf J CommRingCat.{max u v w})
    [SheafOfModules.Localization.HasLowerShriek.{max u v w} (ringSheaf J O)] :
  EnoughFlatObjects
    (ringedSiteModuleCategory.{u, v, max u v w, max u v w} J O) where
  presentation M := ⟨presentation M⟩

end SheafOfModules.RingedSite.FreeFlatCover
