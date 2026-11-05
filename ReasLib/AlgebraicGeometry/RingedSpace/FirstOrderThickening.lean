/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
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

/-- Recover the additive map underlying a morphism of pushed-forward modules by the
presheaf equivalence induced by the homeomorphism underlying a thickening. -/
noncomputable def thickeningPushforwardPreimageAdditive
    {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsIso i.hom.base]
    {F G : X.Modules} (f : (i _*).obj F ⟶ (i _*).obj G) :
    F.val.presheaf ⟶ G.val.presheaf :=
  (TopCat.Presheaf.presheafEquivOfIso AddCommGrpCat
    (asIso i.hom.base)).fullyFaithfulFunctor.preimage
      ((PresheafOfModules.toPresheaf _).map f.val)

/-- Recovering the additive map commutes with pushforward. -/
theorem thickeningPushforwardPreimageAdditive_map
    {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsIso i.hom.base]
    {F G : X.Modules} (f : (i _*).obj F ⟶ (i _*).obj G) :
    Functor.whiskerLeft (TopologicalSpace.Opens.map i.hom.base).op
      (thickeningPushforwardPreimageAdditive i f) =
        (PresheafOfModules.toPresheaf _).map f.val :=
  (TopCat.Presheaf.presheafEquivOfIso AddCommGrpCat
    (asIso i.hom.base)).fullyFaithfulFunctor.map_preimage _

/-- Local surjectivity of the structure map makes the recovered additive map linear. -/
theorem thickeningPushforwardPreimageAdditive_smul
    {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsIso i.hom.base]
    (hsurj : TopCat.Presheaf.IsLocallySurjective i.hom.c)
    {F G : X.Modules} (f : (i _*).obj F ⟶ (i _*).obj G)
    (U : (TopologicalSpace.Opens X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj U) (m : F.val.obj U) :
    (thickeningPushforwardPreimageAdditive i f).app U (r • m) =
      r • (thickeningPushforwardPreimageAdditive i f).app U m := by
  letI : Presheaf.IsLocallySurjective (_root_.Opens.grothendieckTopology X')
      (toRingCatSheafHom i).hom :=
    ⟨fun s => hsurj.imageSieve_mem s⟩
  let M := (PresheafOfModules.pushforward
    (F := TopologicalSpace.Opens.map i.hom.base) (𝟙 _)).obj F.val
  let N := (PresheafOfModules.pushforward
    (F := TopologicalSpace.Opens.map i.hom.base) (𝟙 _)).obj G.val
  let f' : M ⟶ N :=
    (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (toRingCatSheafHom i).hom ((i _*).obj G).isSheaf).symm f.val
  have linear (V : (TopologicalSpace.Opens X')ᵒᵖ) :
      ∀ (r : X.ringCatSheaf.obj.obj ((TopologicalSpace.Opens.map i.hom.base).op.obj V))
        (m : F.val.obj ((TopologicalSpace.Opens.map i.hom.base).op.obj V)),
      (thickeningPushforwardPreimageAdditive i f).app
          ((TopologicalSpace.Opens.map i.hom.base).op.obj V) (r • m) =
        r • (thickeningPushforwardPreimageAdditive i f).app
          ((TopologicalSpace.Opens.map i.hom.base).op.obj V) m := by
    intro r m
    have h := congrArg (fun t => t.app V) (thickeningPushforwardPreimageAdditive_map i f)
    change (thickeningPushforwardPreimageAdditive i f).app
      ((TopologicalSpace.Opens.map i.hom.base).op.obj V) = _ at h
    rw [h]
    exact (f'.app V).hom.map_smul r m
  let e := TopologicalSpace.Opens.mapMapIso
    (asIso i.hom.base)
  have hU : (TopologicalSpace.Opens.map i.hom.base).op.obj
      (Opposite.op (e.inverse.obj U.unop)) = U := by
    apply Opposite.unop_injective
    exact le_antisymm (leOfHom (e.counitIso.app U.unop).hom)
      (leOfHom (e.counitIso.app U.unop).inv)
  have h := linear (Opposite.op (e.inverse.obj U.unop))
  rw [hU] at h
  exact h r m

set_option maxHeartbeats 800000 in
/-- The explicit inverse on Hom sets for module pushforward along a homeomorphism with
locally surjective structure-sheaf map. No nilpotence condition is needed. -/
noncomputable def thickeningPushforwardFullyFaithful
    {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsIso i.hom.base]
    (hsurj : TopCat.Presheaf.IsLocallySurjective i.hom.c) :
    (i _*).FullyFaithful where
  preimage f :=
    ⟨PresheafOfModules.homMk (thickeningPushforwardPreimageAdditive i f)
      (thickeningPushforwardPreimageAdditive_smul i hsurj f)⟩
  map_preimage f := by
    ext U m
    exact congrArg (fun t => t.app U m) (thickeningPushforwardPreimageAdditive_map i f)
  preimage_map f := by
    apply (SheafOfModules.fullyFaithfulForget _).map_injective
    apply (PresheafOfModules.toPresheaf _).map_injective
    change thickeningPushforwardPreimageAdditive i ((i _*).map f) =
      (PresheafOfModules.toPresheaf _).map f.val
    exact (TopCat.Presheaf.presheafEquivOfIso AddCommGrpCat
      (asIso i.hom.base)).fullyFaithfulFunctor.preimage_map
        ((PresheafOfModules.toPresheaf _).map f.val)

/-- The counit isomorphism along a thickening, with inverse constructed by recovering the
adjunction unit through the explicit inverse on Hom sets. -/
noncomputable def thickeningCounitIso
    {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsThickening i] (F : X.Modules) :
    (i ^*).obj ((i _*).obj F) ≅ F := by
  letI : IsIso i.hom.base := IsThickening.base_isIso (i := i)
  let h := thickeningPushforwardFullyFaithful i (IsThickening.c_locallySurjective (i := i))
  let adj := pullbackPushforwardAdjunction i
  refine
    { hom := adj.counit.app F
      inv := h.preimage (adj.unit.app ((i _*).obj F))
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · rw [← adj.counit_naturality (h.preimage (adj.unit.app ((i _*).obj F))),
      h.map_preimage]
    exact adj.left_triangle_components ((i _*).obj F)
  · apply h.map_injective
    rw [Functor.map_comp, h.map_preimage, CategoryTheory.Functor.map_id]
    exact adj.right_triangle_components F

/-- The pullback-pushforward counit on a module over the source of a thickening is an
isomorphism. Its inverse is the explicit map in `thickeningCounitIso`. -/
instance instIsIso_counit_app {X X' : RingedSpace.{u}} {i : X ⟶ X'} [IsThickening i]
    {F : X.Modules} :
    IsIso ((pullbackPushforwardAdjunction i).counit.app F) :=
  (thickeningCounitIso (i := i) F).isIso_hom

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
