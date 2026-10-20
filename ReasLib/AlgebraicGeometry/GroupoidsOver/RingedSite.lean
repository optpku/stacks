/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.AssociatedStructureSheaf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StructureSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
noncomputable section
universe u
namespace AlgebraicGeometry.GroupoidsOver
variable {S : Scheme.{u}}

/-- The associated `τ`-ringed site `(𝒳_τ, 𝒪_𝒳)` of a category fibred in
groupoids over `(Sch/S)_fppf`. -/
abbrev associatedRingedSite (𝒳 : GroupoidsOver S) (τ : StandardTopology) :
    RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf (𝒳.associatedTopology τ) (associatedStructureSheaf 𝒳 τ)

/-- The topology of `associatedRingedSite 𝒳 τ` is the associated `τ`-topology of
`𝒳`. -/
theorem associatedRingedSite_siteTopology (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) :
    (associatedRingedSite 𝒳 τ).siteTopology = 𝒳.associatedTopology τ :=
  rfl

/-- The structure sheaf of `associatedRingedSite 𝒳 τ` is `𝒪_𝒳`. -/
theorem associatedRingedSite_structureSheaf (𝒳 : GroupoidsOver S)
    (τ : StandardTopology) :
    (associatedRingedSite 𝒳 τ).structureSheaf = associatedStructureSheaf 𝒳 τ :=
  rfl

/-- At the fppf topology, the associated ringed site equals the canonical fppf ringed site. -/
theorem associatedRingedSite_fppf (𝒳 : GroupoidsOver S) :
    associatedRingedSite 𝒳 .fppf = ringedSite 𝒳 :=
  rfl


end AlgebraicGeometry.GroupoidsOver
