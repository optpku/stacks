/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.CategoryTheory.Sites.Cohomology.Acyclic

/-!
# Acyclicity and module pushforward

This file owns the reusable acyclicity properties of module pushforward along a
morphism of ringed sites.
-/

@[expose] public section

open CategoryTheory

noncomputable section

-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

universe uX vX uY vY w z

namespace RingedSite.Hom.modulePushforward

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}

section Injective

variable [HasSheafify Y.siteTopology AddCommGrpCat.{z}]
variable [HasExt.{z} (Sheaf Y.siteTopology AddCommGrpCat.{z})]

/-- Stacks 072Z: pushforward sends an injective module sheaf to a totally acyclic
underlying abelian sheaf. -/
@[stacks 072Z]
instance isTotallyAcyclic_of_injective
    (f : Hom X Y) (I : ModuleCat.{z} X) [Injective I] :
    Sheaf.IsTotallyAcyclic
      ((SheafOfModules.toSheaf Y.structureSheaf).obj
        (f.modulePushforward.obj I)) := sorry

end Injective

section TotallyAcyclic

variable [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
variable [HasSheafify X.siteTopology AddCommGrpCat.{z}]
variable [HasExt.{z} (Sheaf X.siteTopology AddCommGrpCat.{z})]

/-- Stacks 0731 (4): a module sheaf with totally acyclic underlying abelian sheaf is
bounded-below right acyclic for pushforward. -/
@[stacks 0731 "(4)"]
theorem rightAcyclic_of_isTotallyAcyclic
    (f : Hom X Y) (F : ModuleCat.{z} X)
    [Sheaf.IsTotallyAcyclic
      ((SheafOfModules.toSheaf X.structureSheaf).obj F)] :
    Functor.RightAcyclic.Bounded f.modulePushforward F := sorry

end TotallyAcyclic

end RingedSite.Hom.modulePushforward
