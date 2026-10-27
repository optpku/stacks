/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Projective.Finite
public import ReasLib.CategoryTheory.Filtration.Derived.BoundedQuasiIso
public import Mathlib.CategoryTheory.Localization.Resolution

/-! Resolution and comparison certificates for filtered-projective models. -/

@[expose] public section
open CategoryTheory
noncomputable section
universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable (C : Type u) [_root_.CategoryTheory.Category.{v} C] [Abelian C]
variable [HasDerivedCategory (GradedObject ℤ C)]
variable (h_inverts : AssociatedGraded.Inverts C)

namespace Minus.FilteredProjective

/-- The localizer induced by the inclusion of finite filtered-projective complexes. -/
abbrev projectiveLocalizer :
    LocalizerMorphism
      ((Minus.QuasiIso C).inverseImage
        (Finite.FilteredProjective.inclusion C).mapHomotopyCategoryMinus)
      (Minus.QuasiIso C) := LocalizerMorphism.ofEq rfl

/-- Every bounded-above finite filtered complex admits a projective filtered resolution. -/
theorem hasProjectiveFilteredResolutions [EnoughProjectives C] :
    (projectiveLocalizer C).HasLeftResolutions := sorry

/-- The projective inclusion is localized fully faithful. -/
instance projectiveLocalizerIsLocalizedFullyFaithful [EnoughProjectives C] :
    (projectiveLocalizer C).IsLocalizedFullyFaithful := sorry

end Minus.FilteredProjective
end CategoryTheory.FilteredObject.FiniteDerived
