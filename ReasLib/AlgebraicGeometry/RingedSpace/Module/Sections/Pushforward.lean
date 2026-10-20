/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Objectwise
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sections after direct image

This leaf owns the underived comparison between sections on a preimage open and sections after
direct image.  The comparison is exposed as a natural isomorphism, with objectwise and top-open
specializations for downstream statements.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Sections.Pushforward

variable {X Y : RingedSpace.{u}}

/-- The natural transformation from restricted sections on a preimage open to sections after
direct image. -/
@[stacks 0D6H "sections and direct image"]
noncomputable def comparison (f : X ⟶ Y) (V : Opens Y.carrier) :
    moduleSectionsEvaluationFunctor X (preimageOpen f V) ⋙
        moduleSectionsRestrictionFunctor f V ⟶
      RingedSpace.Hom.pushforward f ⋙ moduleSectionsEvaluationFunctor Y V :=
  RingedSite.Hom.ModuleSections.objectPushforwardNat (opensRingedSiteHom f) V

/-- The sections/direct-image natural transformation is invertible. -/
@[stacks 0D6H "sections and direct image"]
noncomputable instance comparison_isIso (f : X ⟶ Y) (V : Opens Y.carrier) :
    IsIso (comparison f V) := sorry

/-- Sections over `f ⁻¹ᵁ V`, restricted to `Γ(V, 𝒪_Y)`, agree with sections over `V` after
direct image. -/
@[stacks 0D6H "sections and direct image"]
theorem functor_eq (f : X ⟶ Y) (V : Opens Y.carrier) :
    moduleSectionsEvaluationFunctor X (preimageOpen f V) ⋙
        moduleSectionsRestrictionFunctor f V =
      RingedSpace.Hom.pushforward f ⋙ moduleSectionsEvaluationFunctor Y V := sorry

/-- The natural isomorphism between restricted sections on a preimage open and sections after
direct image. -/
@[stacks 0D6H "sections and direct image"]
noncomputable def comparisonIso (f : X ⟶ Y) (V : Opens Y.carrier) :
    moduleSectionsEvaluationFunctor X (preimageOpen f V) ⋙
        moduleSectionsRestrictionFunctor f V ≅
      RingedSpace.Hom.pushforward f ⋙ moduleSectionsEvaluationFunctor Y V :=
  asIso (comparison f V)

/-- The objectwise sections/direct-image isomorphism over an open subset. -/
@[stacks 0D6H "objectwise sections and direct image"]
noncomputable def sectionIso (f : X ⟶ Y) (V : Opens Y.carrier) (F : X.Modules) :
    (moduleSectionsRestrictionFunctor f V).obj
        ((moduleSectionsEvaluationFunctor X (preimageOpen f V)).obj F) ≅
      (moduleSectionsEvaluationFunctor Y V).obj
        ((RingedSpace.Hom.pushforward f).obj F) :=
  (comparisonIso f V).app F

/-- The natural global-sections/direct-image isomorphism, with scalars restricted along
`Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`. -/
@[stacks 0D6H "global sections and direct image"]
noncomputable def globalIso (f : X ⟶ Y) :
    moduleGlobalSectionsFunctor X ⋙ moduleSectionsRestrictionFunctor f ⊤ ≅
      RingedSpace.Hom.pushforward f ⋙ moduleGlobalSectionsFunctor Y :=
  comparisonIso f ⊤

/-- Global sections of a direct image are the source global sections with scalars restricted along
the map on global section rings. -/
@[stacks 0D6H "objectwise global sections and direct image"]
noncomputable def globalSectionIso (f : X ⟶ Y) (F : X.Modules) :
    (moduleSectionsRestrictionFunctor f ⊤).obj
        ((moduleGlobalSectionsFunctor X).obj F) ≅
      (moduleGlobalSectionsFunctor Y).obj
        ((RingedSpace.Hom.pushforward f).obj F) :=
  (globalIso f).app F

end AlgebraicGeometry.RingedSpace.Module.Sections.Pushforward
