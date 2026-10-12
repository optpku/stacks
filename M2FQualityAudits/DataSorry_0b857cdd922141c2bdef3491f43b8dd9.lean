/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Lean

public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_14_4_IdealSubobject

/-!
# Inverse-image ideals on algebraic spaces

The inverse-image ideal of `I ⊂ 𝒪_X` along `f : Y ⟶ X` is the image of the
canonical map `f^* I ⟶ 𝒪_Y` obtained from `f^* I ⟶ f^* 𝒪_X` and the unit
comparison `f^* 𝒪_X ⟶ 𝒪_Y`.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IdealSubobject

/-- The type-valued sheaf underlying the structure module `𝒪_X` compares with the
underlying structure sheaf of the small étale ringed site. -/
noncomputable def unitUnderlyingIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (Sheaf.InternalModule.ToInternal.underlying (structureSheaf X)).obj
      (SheafOfModules.unit (structureSheaf X)) ≅
      RingedSite.Hom.underlyingStructureSheaf (ringedSite X) where
  hom :=
    { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  inv :=
    { hom := { app := fun _ ↦ 𝟙 _, naturality := fun _ _ _ ↦ sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The canonical morphism `𝒪_X ⟶ f_* 𝒪_Y` of `𝒪_X`-modules associated to a
morphism of algebraic spaces. -/
noncomputable def unitToPushforward {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    SheafOfModules.unit (structureSheaf X) ⟶
      (Modules.pushforward f).obj (SheafOfModules.unit (structureSheaf Y)) :=
  Sheaf.InternalModule.homOfUnderlying (structureSheaf X)
    ((unitUnderlyingIso X).hom ≫
      (ringedToposHom f).underlyingDirectImageMap ≫
      (ringedToposHom f).toTopos.pushforward.map (unitUnderlyingIso Y).inv ≫
      (RingedSite.ToposHom.ModulePushforward.forgetIso (ringedToposHom f)).inv.app
        (SheafOfModules.unit (structureSheaf Y)))
    sorry sorry

/-- The canonical comparison `f^* 𝒪_X ⟶ 𝒪_Y` of structure modules. -/
noncomputable def pullbackUnit {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    (Modules.pullback f).obj (SheafOfModules.unit (structureSheaf X)) ⟶
      SheafOfModules.unit (structureSheaf Y) :=
  ((Modules.pullbackPushforwardAdjunction f).homEquiv
      (SheafOfModules.unit (structureSheaf X))
      (SheafOfModules.unit (structureSheaf Y))).symm
    (unitToPushforward f)

/-- `pullbackUnit f` is the adjunct of `unitToPushforward f`. -/
theorem pullbackUnit_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    pullbackUnit f =
      ((Modules.pullbackPushforwardAdjunction f).homEquiv
          (SheafOfModules.unit (structureSheaf X))
          (SheafOfModules.unit (structureSheaf Y))).symm
        (unitToPushforward f) :=
  rfl

/-- The pulled-back ideal map `f^* I ⟶ 𝒪_Y`. -/
noncomputable def pullbackMap {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (I : IdealSubobject X) (f : Y ⟶ X) :
    (Modules.pullback f).obj I.toModule ⟶
      SheafOfModules.unit (structureSheaf Y) :=
  (Modules.pullback f).map I.arrow ≫ pullbackUnit f

/-- `pullbackMap I f` extends the pulled-back inclusion of `I` by `pullbackUnit f`. -/
theorem pullbackMap_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (I : IdealSubobject X) (f : Y ⟶ X) :
    pullbackMap I f = (Modules.pullback f).map I.arrow ≫ pullbackUnit f :=
  rfl

/-- The inverse-image ideal sheaf `f⁻¹I · 𝒪_Y`. -/
noncomputable def pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (I : IdealSubobject X) (f : Y ⟶ X) : IdealSubobject Y :=
  imageSubobject (I.pullbackMap f)

/-- Inverse image of an ideal subobject is the image of `pullbackMap`. -/
theorem pullback_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (I : IdealSubobject X) (f : Y ⟶ X) :
    I.pullback f = imageSubobject (I.pullbackMap f) :=
  rfl

/-- The canonical factorization of a pulled-back ideal map through its image. -/
noncomputable abbrev pullbackFactor {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (I : IdealSubobject X) (f : Y ⟶ X) :
    (Modules.pullback f).obj I.toModule ⟶ (I.pullback f).toModule :=
  factorThruImageSubobject (I.pullbackMap f)

/-- The canonical factorization through the inverse-image ideal recovers the
pulled-back map to the structure sheaf. -/
theorem pullbackFactor_fac {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (I : IdealSubobject X) (f : Y ⟶ X) :
    I.pullbackFactor f ≫ (I.pullback f).arrow = I.pullbackMap f :=
  sorry

/-- The inverse-image ideal is the least ideal through which the pulled-back
ideal map factors. -/
theorem pullback_le_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (I : IdealSubobject X) (f : Y ⟶ X) (J : IdealSubobject Y) :
    I.pullback f ≤ J ↔
      ∃ g : (Modules.pullback f).obj I.toModule ⟶ J.toModule,
        g ≫ J.arrow = I.pullbackMap f :=
  sorry

/-- Inverse image of a quasi-coherent ideal sheaf is quasi-coherent. -/
instance instIsQuasiCoherent_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] (f : Y ⟶ X) :
    IsQuasiCoherent (I.pullback f) :=
  sorry

end IdealSubobject

end AlgebraicGeometry.AlgebraicSpace


namespace M2FDataSorryAudit

open Lean Meta Elab Command

private def containsNonPropSorry (value : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  forEachExpr value fun expr => do
    unless ← found.get do
      let (head, args) := expr.getAppFnArgs
      if head == ``sorryAx && args.size >= 1 then
        unless ← isProp args[0]! do
          found.set true
  found.get

run_cmd do
  let env ← getEnv
  -- `env.constants` also contains imported declarations.  Current-module
  -- declarations are the ones without a `const2ModIdx` entry; restricting the
  -- scan to them is important for remote compilation because `mkModuleData`
  -- materializes and traverses the entire imported environment.  That made a
  -- tiny audit scratch file hit Leanfra's cancellation deadline on large repos.
  for (name, info) in env.constants do
    if (Environment.getModuleIdxFor? env name).isNone then
      if let some value := info.value? true then
        let (hasNonPropSorry, _) ← liftCoreM <| (containsNonPropSorry value).run
        if hasNonPropSorry then
          logInfo m!"M2F_NON_PROP_DATA_SORRY|{privateToUserName name}"

end M2FDataSorryAudit
