/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Ambient
import StacksCheckRecall

/-!
# Definition 18.19.1

Compatibility facade for localization of a ringed site at an object. The localized ringed site is
owned by `ReasLib.AlgebraicGeometry.RingedSite.Localization`; its three module functors are owned
by `ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w z

namespace RingedSite

variable (X : RingedSite.{u, v, w}) (U : X)

/- Definition 18.19.1 (1): the localization at `U` is the ringed slice site with the exact
universe level forced by `Over U`. -/
@[stacks 04IX "(1), localized ringed site"]
#check (X.localization U : RingedSite.{max u v, v, w})

/- Definition 18.19.1 (1): the carrier of the localized ringed site is `C / U`. -/
#check (rfl : (RingedSite.localization X U).carrier = Over U)

/- Definition 18.19.1 (1): its topology is the slice topology. -/
#check (rfl : (RingedSite.localization X U).siteTopology = X.siteTopology.over U)

/- Definition 18.19.1 (1): its structure sheaf is the restriction of `𝒪` to the slice. -/
#check (rfl : (RingedSite.localization X U).structureSheaf = X.structureSheaf.over U)

/- Definition 18.19.1 (2): the localization morphism is presented on sites by the forgetful
functor `X / U ⥤ X`. -/
@[stacks 04IX "(2), site functor"]
#check (Over.forget U : Over U ⥤ X)

section ToposMorphism

variable [UnivLE.{max u v, w}]

/- Definition 18.19.1 (2): localization is the canonical morphism from the localized ringed
topos to the ambient one. -/
@[stacks 04IX "(2), ringed-topos morphism"]
#check (Localization.toAmbient X U : ToposHom (X.localization U) X)

/- Definition 18.19.1 (2): its direct-image structure map is adjoint to the identity
`j_U⁻¹ 𝒪 = 𝒪_U`. -/
@[stacks 04IX "(2), structure map"]
#check (Localization.toAmbientStructureMap X U :
  X.structureSheaf ⟶
    ((Over.forget U).sheafPushforwardCocontinuous RingCat.{w}
      (X.siteTopology.over U) X.siteTopology).obj (X.structureSheaf.over U))

end ToposMorphism

/- The module restriction owner uses the same structure-ring map in direct-image form. -/
#check (SheafOfModules.Localization.restrictionRingHom X.structureSheaf U :
  X.structureSheaf.over U ⟶
    ((Over.forget U).sheafPushforwardContinuous RingCat.{w}
      (X.siteTopology.over U) X.siteTopology).obj X.structureSheaf)

/- Definition 18.19.1 (4): restriction sends `𝒪`-modules on `C` to `𝒪.over U`-modules on
`C / U`. -/
@[stacks 04IX "(4)"]
#check (SheafOfModules.Localization.restriction X.structureSheaf U :
  SheafOfModules.{z} X.structureSheaf ⥤
    SheafOfModules.{z} (X.structureSheaf.over U))

variable (F : SheafOfModules.{z} X.structureSheaf) (V : Over U)

/- Definition 18.19.1 (4): restriction obeys the objectwise rule
`(F|_U)(V ⟶ U) = F(V)`. -/
#check (rfl :
  ((SheafOfModules.Localization.restriction X.structureSheaf U).obj F).val.obj (op V) =
    F.val.obj (op V.left))

section LowerShriek

variable [(SheafOfModules.Localization.restriction X.structureSheaf U :
  SheafOfModules.{z} X.structureSheaf ⥤
    SheafOfModules.{z} (X.structureSheaf.over U)).IsRightAdjoint]

/- Definition 18.19.1 (5): extension by zero is the left adjoint of restriction. Its existence
and exactness are supplied by the subsequent lemmas. -/
@[stacks 04IX "(5)"]
#check (SheafOfModules.Localization.lowerShriekRestrictionAdj X.structureSheaf U :
  SheafOfModules.Localization.lowerShriek X.structureSheaf U ⊣
    SheafOfModules.Localization.restriction X.structureSheaf U)

end LowerShriek

section DirectImage

variable [(SheafOfModules.Localization.restriction X.structureSheaf U :
  SheafOfModules.{z} X.structureSheaf ⥤
    SheafOfModules.{z} (X.structureSheaf.over U)).IsLeftAdjoint]

/- Definition 18.19.1 (3): direct image sends modules on the localized ringed site back to
modules on the original ringed site. -/
@[stacks 04IX "(3)"]
#check (SheafOfModules.Localization.directImage X.structureSheaf U :
  SheafOfModules.{z} (X.structureSheaf.over U) ⥤
    SheafOfModules.{z} X.structureSheaf)

/- The restriction/direct-image adjunction records the canonical role of `j_{U*}`. -/
#check (SheafOfModules.Localization.restrictionDirectImageAdj X.structureSheaf U :
  SheafOfModules.Localization.restriction X.structureSheaf U ⊣
    SheafOfModules.Localization.directImage X.structureSheaf U)

end DirectImage

end RingedSite
