/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sets.Closeds
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Subset

/-!
# Module sheaves on closed subspaces

This module presents the subset restriction API using the canonical bundled type
`TopologicalSpace.Closeds X`. Bundling closedness keeps proof parameters out of downstream functor
and instance interfaces.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules.ClosedSubset

variable {X : TopCat.{u}} (𝒪 : X.Sheaf RingCat.{u}) (Z : Closeds X)

/-- The inclusion of a closed subspace into its ambient topological space. -/
abbrev inclusion (Z : Closeds X) : TopCat.subsetSpace (Z : Set X) ⟶ X :=
  Subset.inclusion (Z : Set X)

/-- The restriction of a sheaf of rings to a closed subspace. -/
abbrev ringSheaf : (TopCat.subsetSpace (Z : Set X)).Sheaf RingCat.{u} :=
  Subset.ringSheaf 𝒪 (Z : Set X)

/-- The category of modules over the restriction of `𝒪` to a closed subspace. -/
abbrev Modules :=
  Subset.Modules 𝒪 (Z : Set X)

/-- The canonical map from `𝒪` to the direct image of its restriction to a closed subspace. -/
abbrev structureMap :
    𝒪 ⟶ (TopCat.Sheaf.pushforward RingCat.{u} (inclusion Z)).obj (ringSheaf 𝒪 Z) :=
  Subset.structureSheafHom 𝒪 (Z : Set X)

/-- Restriction of module sheaves to a closed subspace. -/
abbrev pullback : SheafOfModules 𝒪 ⥤ Modules 𝒪 Z :=
  Subset.pullback 𝒪 (Z : Set X)

/-- Direct image of module sheaves from a closed subspace. -/
noncomputable abbrev pushforward : Modules 𝒪 Z ⥤ SheafOfModules 𝒪 :=
  Subset.pushforward 𝒪 (Z : Set X)

/-- Direct image of module sheaves from a closed subspace is additive. -/
noncomputable instance pushforward_additive : (pushforward 𝒪 Z).Additive := inferInstance

end SheafOfModules.ClosedSubset
