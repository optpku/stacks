/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.KernelAnnihilation
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Topos
public import ReasLib.CategoryTheory.Sites.Topos.ClosedImmersion.Exactness
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Modules under a closed immersion of ringed topoi

The underlying morphism of topoi is assumed to be a closed immersion, while the structure-sheaf
map is separately assumed to be epic. The resulting module API is attached to the canonical
`RingedSite.Hom.modulePushforward` functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe uX vX uY vY w z

namespace RingedSite.Hom.ModulePushforward

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vX, z}]
variable (f : X.Hom Y)

/-- The base functor is continuous with the certificate stored in the ringed-site morphism. -/
-- Local instance justification (defeq pin): pin continuity to f.base_isContinuous so IsAnnihilatedByKernel elaborates with the certificate stored in f.structureSheafMap.
local instance baseIsContinuous : f.base.IsContinuous Y.siteTopology X.siteTopology :=
  f.base_isContinuous
variable [PreservesFiniteLimits (f.sheafPullback (A := Type z))]

/-- Module pushforward is exact when the underlying morphism of topoi is a closed immersion;
epimorphy of the structure map is not needed. -/
@[stacks 08M3 "(1)"]
theorem exact_of_closedImmersion [IsClosedImmersion f.toMorphismOfTopoi] :
    exactFunctor
      (ModuleCat.{z} X) (ModuleCat.{z} Y)
      f.modulePushforward.{z} := sorry

/-- Module pushforward is full when the underlying topos morphism is a closed immersion and the
structure-sheaf map is epic. -/
instance full_of_closedImmersion_of_epi
    [IsClosedImmersion f.toMorphismOfTopoi] [Epi f.structureSheafMap] :
    f.modulePushforward.{z}.Full := sorry

/-- Module pushforward is faithful when the underlying topos morphism is a closed immersion and
the structure-sheaf map is epic. -/
instance faithful_of_closedImmersion_of_epi
    [IsClosedImmersion f.toMorphismOfTopoi] [Epi f.structureSheafMap] :
    f.modulePushforward.{z}.Faithful := sorry

/-- Module pushforward is fully faithful when the underlying topos morphism is a closed immersion
and the structure-sheaf map is epic. -/
@[stacks 08M3 "(2)"]
noncomputable def fullyFaithful_of_closedImmersion_of_epi
    [IsClosedImmersion f.toMorphismOfTopoi] [Epi f.structureSheafMap] :
    f.modulePushforward.{z}.FullyFaithful :=
  .ofFullyFaithful f.modulePushforward

/-- The essential image of module pushforward consists exactly of the target module sheaves
annihilated by the kernel of the structure-sheaf map. -/
@[stacks 08M3 "(3)"]
theorem mem_essImage_iff_isAnnihilatedByKernel
    [IsClosedImmersion f.toMorphismOfTopoi] [Epi f.structureSheafMap]
    (G : ModuleCat.{z} Y) :
    f.modulePushforward.{z}.essImage G ↔
      SheafOfModules.IsAnnihilatedByKernel f.structureSheafMap G := sorry

end RingedSite.Hom.ModulePushforward
