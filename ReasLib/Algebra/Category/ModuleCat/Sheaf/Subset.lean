/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.OpenSubset
public import ReasLib.Topology.Category.TopCat.Subset

/-!
# Module sheaves on subspaces

This module owns restriction and direct image for module sheaves along the canonical inclusion of
an arbitrary subset. Closed-support constructions belong to the closed-subset layer built on top
of this file.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules.Subset

variable {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u}) (Z : Set X)

/-- The inclusion of a subspace into its ambient topological space. -/
abbrev inclusion (Z : Set X) : TopCat.subsetSpace Z ⟶ X :=
  TopCat.subsetInclusion Z

/-- The restriction of a sheaf of rings to a subspace. -/
abbrev ringSheaf : (TopCat.subsetSpace Z).Sheaf RingCat.{u} :=
  (TopCat.Sheaf.pullback RingCat.{u} (inclusion Z)).obj 𝒪

/-- The category of modules over the restriction of `𝒪` to a subspace. -/
abbrev Modules :=
  SheafOfModules (ringSheaf 𝒪 Z)

/-- The canonical map from `𝒪` to the direct image of its restriction to a subspace. -/
abbrev structureSheafHom :
    𝒪 ⟶ (TopCat.Sheaf.pushforward RingCat.{u} (inclusion Z)).obj (ringSheaf 𝒪 Z) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} (inclusion Z)).unit.app 𝒪

/-- Restriction of module sheaves to a subspace. -/
abbrev pullback : SheafOfModules 𝒪 ⥤ Modules 𝒪 Z :=
  SheafOfModules.pullback (structureSheafHom 𝒪 Z)

/-- Direct image of module sheaves from a subspace. -/
noncomputable abbrev pushforward : Modules 𝒪 Z ⥤ SheafOfModules 𝒪 :=
  SheafOfModules.pushforward (structureSheafHom 𝒪 Z)

/-- Direct image of module sheaves from a subspace is additive. -/
noncomputable instance pushforward_additive : (pushforward 𝒪 Z).Additive := sorry

end SheafOfModules.Subset
