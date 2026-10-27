/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SquareZeroExtension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pushforward.Composition
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening

/-!
# First-order thickenings of ringed spaces

A first-order thickening is a thickening of ringed spaces whose kernel ideal sheaf is square
zero. A morphism of thickenings of a fixed ringed space induces a map of kernel ideals.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

open Hom

/-- A first-order thickening of ringed spaces is a thickening whose kernel ideal sheaf has
square zero. -/
class IsFirstOrderThickening {X X' : RingedSpace.{u}} (i : X ⟶ X') : Prop
    extends IsThickening i where
  /-- The kernel of `i^♯` has square zero. -/
  square_zero :
    SheafOfModules.RingedSite.KernelIdeal.IsSquareZero (Hom.commRingSheafPushforwardMap i)

/-- Bundling a first-order thickening preserves its first-order property. -/
theorem isFirstOrderThickening_ofHom {Y Y' : RingedSpace.{u}}
    (i : Y ⟶ Y') [IsFirstOrderThickening i] :
    IsFirstOrderThickening (Thickening.of i).hom :=
  (Thickening.of_hom i).symm ▸ (inferInstance : IsFirstOrderThickening i)

/-- The canonical bundled thickening of a first-order thickening is first order. -/
instance instIsFirstOrderThickening_ofHom {Y Y' : RingedSpace.{u}}
    (i : Y ⟶ Y') [IsFirstOrderThickening i] :
    IsFirstOrderThickening (Thickening.of i).hom :=
  isFirstOrderThickening_ofHom i

/-- A ringed-space morphism is a first-order thickening iff it is a thickening and its kernel
ideal sheaf is square zero. -/
theorem isFirstOrderThickening_iff {X X' : RingedSpace.{u}} (i : X ⟶ X') :
    IsFirstOrderThickening i ↔
      IsThickening i ∧
        SheafOfModules.RingedSite.KernelIdeal.IsSquareZero
          (Hom.commRingSheafPushforwardMap i) := sorry

/-- The identity morphism of a ringed space is a first-order thickening. -/
instance instIsFirstOrderThickeningId (X : RingedSpace.{u}) :
    IsFirstOrderThickening (𝟙 X) := sorry

/-- The underlying map of a first-order thickening is an isomorphism of topological spaces. -/
instance instIsIso_base {X X' : RingedSpace.{u}} {i : X ⟶ X'}
    [h : IsFirstOrderThickening i] : IsIso i.hom.base :=
  h.base_isIso

/-- The pullback-pushforward counit on a module over the source of a thickening is an
isomorphism. -/
instance instIsIso_counit_app {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsThickening i]
    {F : X.Modules} :
    IsIso ((SheafOfModules.pullbackPushforwardAdjunction (toRingCatSheafHom i)).counit.app F) := sorry

namespace Hom

/-- The kernel ideal of a first-order thickening, viewed as an `𝒪_X`-module by inverse image. -/
noncomputable abbrev idealModule {X X' : RingedSpace.{u}} (i : X ⟶ X') : X.Modules :=
  (i ^*).obj (kernelIdealSheaf i)

/-- Inverse image recovers the kernel ideal sheaf of a first-order thickening as an
`𝒪_X`-module. -/
theorem idealModule_eq {X X' : RingedSpace.{u}} (i : X ⟶ X') :
    idealModule i = (i ^*).obj (kernelIdealSheaf i) := sorry

/-- The comparison `ℐ_2 ⟶ h_* ℐ_1` is killed by the cokernel of `h_*` of the kernel-ideal
inclusion. -/
theorem kernelIdealPushforwardMap_comp_cokernel
    {X X1 X2 : RingedSpace.{u}} (i1 : X ⟶ X1) (h : X1 ⟶ X2) :
    (kernelIdealι (i1 ≫ h) ≫
        SheafOfModules.unitToPushforwardObjUnit (toRingCatSheafHom h)) ≫
      cokernel.π ((h _*).map (kernelIdealι i1)) = 0 := sorry

/-- The `𝒪_{X'_2}`-linear comparison `ℐ_2 ⟶ h_* ℐ_1` induced by `h^♯`. -/
noncomputable def kernelIdealPushforwardMap
    {X X1 X2 : RingedSpace.{u}} {i1 : X ⟶ X1} {i2 : X ⟶ X2}
    (h : X1 ⟶ X2) (w : i1 ≫ h = i2) :
    kernelIdealSheaf i2 ⟶ (h _*).obj (kernelIdealSheaf i1) :=
  match i2, w with
  | _, rfl =>
      Abelian.monoLift ((h _*).map (kernelIdealι i1))
        (kernelIdealι (i1 ≫ h) ≫
          SheafOfModules.unitToPushforwardObjUnit (toRingCatSheafHom h))
        (kernelIdealPushforwardMap_comp_cokernel i1 h)

/-- The comparison of kernel ideals along a composite thickening, as `𝒪_X`-modules. -/
noncomputable def idealMapComp {X X1 X2 : RingedSpace.{u}} (i1 : X ⟶ X1) (h : X1 ⟶ X2) :
    idealModule (i1 ≫ h) ⟶ idealModule i1 :=
  ((i1 ≫ h) ^*).map (kernelIdealPushforwardMap h rfl) ≫
    (pullbackCompIso i1 h).hom.app ((h _*).obj (kernelIdealSheaf i1)) ≫
      (i1 ^*).map ((pullbackPushforwardAdjunction h).counit.app (kernelIdealSheaf i1))

/-- `h^♯` induces an `𝒪_X`-module map `ℐ_2 ⟶ ℐ_1` of kernel ideals of first-order
thickenings of `X`. -/
noncomputable def idealMap {X X1 X2 : RingedSpace.{u}} {i1 : X ⟶ X1} {i2 : X ⟶ X2}
    (h : X1 ⟶ X2) (w : i1 ≫ h = i2) :
    idealModule i2 ⟶ idealModule i1 :=
  match i2, w with
  | _, rfl => idealMapComp i1 h

/-- The identity morphism of a thickening induces the identity on kernel ideals. -/
theorem idealMap_id {X X' : RingedSpace.{u}} (i : X ⟶ X') :
    idealMap (𝟙 X') (Category.comp_id i) = 𝟙 (idealModule i) := sorry

/-- Kernel-ideal maps of composable morphisms of thickenings compose. -/
theorem idealMapComp_comp {X X1 X2 X3 : RingedSpace.{u}}
    (i1 : X ⟶ X1) (h12 : X1 ⟶ X2) (h23 : X2 ⟶ X3) :
    idealMapComp i1 (h12 ≫ h23) =
      idealMapComp (i1 ≫ h12) h23 ≫ idealMapComp i1 h12 := sorry

end Hom

end AlgebraicGeometry.RingedSpace
