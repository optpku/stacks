/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedImmersion
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
public import ReasLib.AlgebraicGeometry.RingedSite.Topos
public import ReasLib.CategoryTheory.Sites.Topos.ClosedImmersion.Basic

/-!
# The topos morphism underlying a closed immersion of ringed spaces

This file connects the geometric closed-embedding and locally-surjective hypotheses for a
morphism of ringed spaces to the corresponding properties of its opens-ringed-site morphism.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.ClosedImmersion

variable {X Z : RingedSpace.{u}} (i : Z ⟶ X)

/-- A closed embedding of the underlying spaces induces a closed immersion of the topoi
presented by their opens sites. -/
theorem of_isClosedEmbedding
    (hi : Topology.IsClosedEmbedding i.hom.base) :
    CategoryTheory.MorphismOfTopoiIn.IsClosedImmersion
      (RingedSpace.opensMorphismOfTopoi i) := sorry

/-- The topos morphism presented by a closed immersion of ringed spaces is canonically a closed
immersion. -/
theorem of_isClosedImmersion
    [RingedSpace.IsClosedImmersion i] :
    CategoryTheory.MorphismOfTopoiIn.IsClosedImmersion
      (RingedSpace.opensMorphismOfTopoi i) := sorry

/-- A locally surjective structure-sheaf map is an epimorphism after forgetting from
commutative-ring sheaves to ring sheaves. -/
theorem structureSheafMap_epi
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)] :
    Epi (RingedSpace.opensRingedSiteHom i).structureSheafMap := sorry

end AlgebraicGeometry.RingedSpace.Hom.ClosedImmersion
