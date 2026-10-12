/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Exact
public import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of modules on a commutative ringed site

This file is the commutative-ringed-site view of the coefficient-generic localization API.
It names the adjoint triple attached to an object `U` without rebuilding any of its data:
`lowerShriek 𝒪 U ⊣ restriction 𝒪 U ⊣ directImage 𝒪 U`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite.Localization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Restriction of module sheaves to the localization of a commutative ringed site at `U`. -/
@[stacks 04IX "commutative ringed-site restriction"]
abbrev restriction (𝒪 : Sheaf J CommRingCat.{w}) (U : C) :=
  SheafOfModules.Localization.restriction (ringSheaf J 𝒪) U

section LowerShriek

variable (𝒪 : Sheaf J CommRingCat.{w}) (U : C)
variable [(SheafOfModules.Localization.restriction
  (ringSheaf J 𝒪) U : SheafOfModules.{z} (ringSheaf J 𝒪) ⥤
    SheafOfModules.{z} ((ringSheaf J 𝒪).over U)).IsRightAdjoint]

/-- Extension by zero `j_!` from the localization at `U`. -/
@[stacks 04IX "commutative ringed-site lower shriek"]
abbrev lowerShriek :=
  SheafOfModules.Localization.lowerShriek (ringSheaf J 𝒪) U

/-- The canonical adjunction `j_! ⊣ j^*` for localization at an object. -/
@[stacks 03DI "commutative ringed-site lower-shriek adjunction"]
noncomputable abbrev lowerShriekRestrictionAdj :
    lowerShriek 𝒪 U ⊣ restriction 𝒪 U :=
  SheafOfModules.Localization.lowerShriekRestrictionAdj (ringSheaf J 𝒪) U

/-- The Hom equivalence characterizing `j_! ⊣ j^*` on a commutative ringed site. -/
@[stacks 03DI "commutative ringed-site lower-shriek Hom equivalence"]
noncomputable abbrev lowerShriekHomEquiv
    (G : SheafOfModules.{z} ((ringSheaf J 𝒪).over U))
    (F : SheafOfModules.{z} (ringSheaf J 𝒪)) :
    ((lowerShriek 𝒪 U).obj G ⟶ F) ≃ (G ⟶ (restriction 𝒪 U).obj F) :=
  SheafOfModules.Localization.lowerShriekHomEquiv (ringSheaf J 𝒪) U G F

end LowerShriek

section DirectImage

variable (𝒪 : Sheaf J CommRingCat.{w}) (U : C)
variable [(SheafOfModules.Localization.restriction
  (ringSheaf J 𝒪) U : SheafOfModules.{z} (ringSheaf J 𝒪) ⥤
    SheafOfModules.{z} ((ringSheaf J 𝒪).over U)).IsLeftAdjoint]

/-- Direct image `j_*` from the localization at `U`. -/
@[stacks 04IX "commutative ringed-site direct image"]
abbrev directImage :=
  SheafOfModules.Localization.directImage (ringSheaf J 𝒪) U

/-- The canonical adjunction `j^* ⊣ j_*` for localization at an object. -/
@[stacks 04IX "commutative ringed-site direct-image adjunction"]
noncomputable abbrev restrictionDirectImageAdj :
    restriction 𝒪 U ⊣ directImage 𝒪 U :=
  SheafOfModules.Localization.restrictionDirectImageAdj (ringSheaf J 𝒪) U

/-- The Hom equivalence characterizing `j^* ⊣ j_*` on a commutative ringed site. -/
@[stacks 04IX "commutative ringed-site direct-image Hom equivalence"]
noncomputable abbrev restrictionDirectImageHomEquiv
    (F : SheafOfModules.{z} (ringSheaf J 𝒪))
    (G : SheafOfModules.{z} ((ringSheaf J 𝒪).over U)) :
    ((restriction 𝒪 U).obj F ⟶ G) ≃ (F ⟶ (directImage 𝒪 U).obj G) :=
  SheafOfModules.Localization.restrictionDirectImageHomEquiv
    (ringSheaf J 𝒪) U F G

end DirectImage

section LocalProperties

variable (𝒪 : Sheaf J CommRingCat.{w})

/-- A morphism of module sheaves is an isomorphism if its restrictions to a family covering the
terminal object are isomorphisms.  This is the module-sheaf presentation bridge to
`CategoryTheory.Sheaf.isIso_of_coversTop`. -/
@[stacks 04IX "cover-local detection of module-sheaf isomorphisms"]
theorem isIso_of_coversTop
    {I : Type*} {X : I → C} (hX : J.CoversTop X)
    {F G : ringedSiteModuleCategory.{u, v, z, w} J 𝒪} {f : F ⟶ G}
    (h : ∀ i, IsIso ((restriction 𝒪 (X i)).map f)) :
    IsIso f := sorry

/-- A module-sheaf morphism is an isomorphism exactly when its restrictions to the members of a
fixed covering family are isomorphisms. -/
@[stacks 04IX "cover-local characterization of module-sheaf isomorphisms"]
theorem isIso_iff_of_coversTop
    {I : Type*} {X : I → C} (hX : J.CoversTop X)
    {F G : ringedSiteModuleCategory.{u, v, z, w} J 𝒪} (f : F ⟶ G) :
    IsIso f ↔ ∀ i, IsIso ((restriction 𝒪 (X i)).map f) := sorry

end LocalProperties

section RingedSiteView

variable (𝒪 : Sheaf J CommRingCat.{w}) (U : C)

end RingedSiteView

end SheafOfModules.RingedSite.Localization
