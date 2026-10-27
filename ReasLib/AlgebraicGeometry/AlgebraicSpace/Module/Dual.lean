/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallAtlas
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal

/-!
# Dual modules on algebraic spaces in the original universe

The full étale site has objects in `Type (u + 1)`, so its literal slice-Hom
carrier need not lie in `Type u`. We restrict that construction to the existing
small dense atlas site. A section is a compatible family of linear functionals
on all atlas charts over the given chart; restriction is precomposition of the
chart arrow. No dual object or morphism is selected from an existence assertion.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PullbackFactory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The existing small atlas site supplied by the algebraic-space input. -/
abbrev dualSite (X : AlgebraicSpace S) :=
  SmallAtlas.Site (AtlasInput.scheme X) (AtlasInput.map X)

/-- The actual full inclusion of the small atlas charts in the étale site. -/
abbrev dualInclusion (X : AlgebraicSpace S) : dualSite X ⥤ smallEtaleSite X :=
  SmallAtlas.inclusion (AtlasInput.scheme X) (AtlasInput.map X)

/-- A chartwise linear functional, with scalars restricted along its arrow to `U`. -/
abbrev dualComponent (E : X.Modules) (U : smallEtaleSite X) (V : dualSite X)
    (f : (dualInclusion X).obj V ⟶ U) :
    ModuleCat ((commStructureSheaf X).obj.obj (op U)) :=
  (ModuleCat.restrictScalars ((commStructureSheaf X).obj.map f.op).hom).obj
    (ModuleCat.of ((commStructureSheaf X).obj.obj (op ((dualInclusion X).obj V)))
      (((toCommModules X).obj E).val.obj (op ((dualInclusion X).obj V)) →ₗ[
        (commStructureSheaf X).obj.obj (op ((dualInclusion X).obj V))]
        (commStructureSheaf X).obj.obj (op ((dualInclusion X).obj V))))

/-- Families of chartwise linear functionals indexed entirely in universe `u`. -/
abbrev dualFamilies (E : X.Modules) (U : smallEtaleSite X) :=
  ∀ (V : dualSite X) (f : (dualInclusion X).obj V ⟶ U), dualComponent E U V f

/-- Recover the unchanged chartwise linear functional after restricting its scalars. -/
def dualComponentMap (E : X.Modules) (U : smallEtaleSite X) (V : dualSite X)
    (f : (dualInclusion X).obj V ⟶ U) (s : dualComponent E U V f) :
    ((toCommModules X).obj E).val.obj (op ((dualInclusion X).obj V)) →ₗ[
      (commStructureSheaf X).obj.obj (op ((dualInclusion X).obj V))]
      (commStructureSheaf X).obj.obj (op ((dualInclusion X).obj V)) := s

/-- Compatibility is naturality for all arrows of the full small atlas slice. -/
def DualCompatible (E : X.Modules) (U : smallEtaleSite X) (s : dualFamilies E U) : Prop :=
  ∀ (V W : dualSite X) (h : V ⟶ W) (f : (dualInclusion X).obj W ⟶ U)
    (x : ((toCommModules X).obj E).val.obj (op ((dualInclusion X).obj W))),
    (commStructureSheaf X).obj.map ((dualInclusion X).map h).op
      (dualComponentMap E U W f (s W f) x) =
      dualComponentMap E U V ((dualInclusion X).map h ≫ f) (s V ((dualInclusion X).map h ≫ f))
        (((toCommModules X).obj E).val.map ((dualInclusion X).map h).op x)

/-- Zero functionals are compatible with chart restriction. -/
theorem dualCompatible_zero (E : X.Modules) (U : smallEtaleSite X) :
    DualCompatible E U 0 := by
  intro V W h f x
  change (commStructureSheaf X).obj.map ((dualInclusion X).map h).op 0 = 0
  exact map_zero _

/-- Compatible families are closed under pointwise addition. -/
theorem dualCompatible_add (E : X.Modules) (U : smallEtaleSite X)
    (s t : dualFamilies E U) (hs : DualCompatible E U s) (ht : DualCompatible E U t) :
    DualCompatible E U (s + t) := by
  intro V W h f x
  change (commStructureSheaf X).obj.map ((dualInclusion X).map h).op
    (dualComponentMap E U W f (s W f) x + dualComponentMap E U W f (t W f) x) = _
  rw [map_add, hs V W h f x, ht V W h f x]
  rfl

/-- Scalar restriction from `U` preserves compatibility of linear functionals. -/
theorem dualCompatible_smul (E : X.Modules) (U : smallEtaleSite X)
    (r : (commStructureSheaf X).obj.obj (op U)) (s : dualFamilies E U)
    (hs : DualCompatible E U s) : DualCompatible E U (r • s) := by
  intro V W h f x
  change (commStructureSheaf X).obj.map ((dualInclusion X).map h).op
    ((commStructureSheaf X).obj.map f.op r * dualComponentMap E U W f (s W f) x) =
      (commStructureSheaf X).obj.map (((dualInclusion X).map h) ≫ f).op r *
        dualComponentMap E U V ((dualInclusion X).map h ≫ f)
          (s V ((dualInclusion X).map h ≫ f))
          (((toCommModules X).obj E).val.map ((dualInclusion X).map h).op x)
  rw [map_mul, hs V W h f x, op_comp, Functor.map_comp]
  rfl

/-- The submodule of compatible chartwise linear functionals. -/
def dualSections (E : X.Modules) (U : smallEtaleSite X) :
    Submodule ((commStructureSheaf X).obj.obj (op U)) (dualFamilies E U) where
  carrier := {s | DualCompatible E U s}
  zero_mem' := dualCompatible_zero E U
  add_mem' := fun {s t} => dualCompatible_add E U s t
  smul_mem' := dualCompatible_smul E U

/-- Full slice morphisms from `E` to the structure module: the unshrunk internal-Hom
sections before restriction to the small dense family of charts. -/
abbrev dualSliceHom (E : X.Modules) (U : smallEtaleSite X) :=
  ((toCommModules X).obj E).over U ⟶ (SheafOfModules.unit (commRingSheaf X)).over U

/-- Restrict an actual slice morphism to its linear maps on the specified charts. -/
def dualFromSliceFamily (E : X.Modules) (U : smallEtaleSite X)
    (s : dualSliceHom E U) : dualFamilies E U :=
  fun _ f => (s.val.app (op (Over.mk f))).hom

/-- Naturality of a slice morphism gives the displayed compatibility equations. -/
theorem dualFromSliceFamily_compatible (E : X.Modules) (U : smallEtaleSite X)
    (s : dualSliceHom E U) : DualCompatible E U (dualFromSliceFamily E U s) := by
  intro V W h f x
  exact (PresheafOfModules.naturality_apply s.val
    (Over.homMk ((dualInclusion X).map h) (by rfl) :
      Over.mk ((dualInclusion X).map h ≫ f) ⟶ Over.mk f).op x).symm

/-- The fixed restriction map from actual internal-Hom sections to the small carrier. -/
def dualFromSliceHom (E : X.Modules) (U : smallEtaleSite X)
    (s : dualSliceHom E U) : dualSections E U :=
  ⟨dualFromSliceFamily E U s, dualFromSliceFamily_compatible E U s⟩

/-- Fullness and cover density of the same small atlas inclusion make the fixed
restriction map bijective on each slice; no inverse is selected by the definition of dual. -/
theorem dualFromSliceHom_bijective (E : X.Modules) (U : smallEtaleSite X) :
    Function.Bijective (dualFromSliceHom E U) := sorry

/-- Precomposing chart arrows restricts a compatible family to the source chart. -/
theorem dualRestrict_compatible (E : X.Modules) {U V : smallEtaleSite X}
    (i : V ⟶ U) (s : dualSections E U) :
    DualCompatible E V (fun W f => s.val W (f ≫ i)) := by
  intro W W' h f x
  change (commStructureSheaf X).obj.map ((dualInclusion X).map h).op
      (dualComponentMap E U W' (f ≫ i) (s.val W' (f ≫ i)) x) =
    dualComponentMap E U W (((dualInclusion X).map h ≫ f) ≫ i)
      (s.val W (((dualInclusion X).map h ≫ f) ≫ i))
      (((toCommModules X).obj E).val.map ((dualInclusion X).map h).op x)
  rw [Category.assoc]
  exact s.property W W' h (f ≫ i) x

/-- Restriction retains each specified functional and only composes the chart arrow. -/
def dualRestrictFun (E : X.Modules) {U V : smallEtaleSite X} (i : V ⟶ U)
    (s : dualSections E U) : dualSections E V :=
  ⟨fun W f => s.val W (f ≫ i), dualRestrict_compatible E i s⟩

/-- Restriction of compatible families preserves addition. -/
theorem dualRestrictFun_add (E : X.Modules) {U V : smallEtaleSite X} (i : V ⟶ U)
    (s t : dualSections E U) :
    dualRestrictFun E i (s + t) = dualRestrictFun E i s + dualRestrictFun E i t := by
  apply Subtype.ext
  rfl

/-- Restriction of compatible families is semilinear over restriction of sections. -/
theorem dualRestrictFun_smul (E : X.Modules) {U V : smallEtaleSite X} (i : V ⟶ U)
    (r : (commStructureSheaf X).obj.obj (op U)) (s : dualSections E U) :
    dualRestrictFun E i (r • s) =
      (commStructureSheaf X).obj.map i.op r • dualRestrictFun E i s := by
  apply Subtype.ext
  funext W f
  apply LinearMap.ext
  intro x
  change (commStructureSheaf X).obj.map (f ≫ i).op r *
      dualComponentMap E U W (f ≫ i) (s.val W (f ≫ i)) x =
    (commStructureSheaf X).obj.map f.op ((commStructureSheaf X).obj.map i.op r) *
      dualComponentMap E U W (f ≫ i) (s.val W (f ≫ i)) x
  rw [op_comp, Functor.map_comp]
  rfl

/-- The original-universe module of dual sections over an étale chart. -/
def dualObj (E : X.Modules) (U : (smallEtaleSite X)ᵒᵖ) :
    ModuleCat.{u} ((commStructureSheaf X).obj.obj U) :=
  ModuleCat.of _ (dualSections E U.unop)

/-- The semilinear restriction map on the displayed dual section modules. -/
def dualRestrict (E : X.Modules) {U V : (smallEtaleSite X)ᵒᵖ} (i : U ⟶ V) :
    dualObj E U ⟶
      (ModuleCat.restrictScalars ((commStructureSheaf X).obj.map i).hom).obj (dualObj E V) :=
  ModuleCat.ofHom
    (X := dualObj E U)
    (Y := (ModuleCat.restrictScalars ((commStructureSheaf X).obj.map i).hom).obj (dualObj E V))
    { toFun := dualRestrictFun E i.unop
      map_add' := dualRestrictFun_add E i.unop
      map_smul' := dualRestrictFun_smul E i.unop }

/-- Identity restriction is the identity scalar-restriction map. -/
theorem dualRestrict_id (E : X.Modules) (U : (smallEtaleSite X)ᵒᵖ) :
    dualRestrict E (𝟙 U) =
      (ModuleCat.restrictScalarsId' ((commStructureSheaf X).obj.map (𝟙 U)).hom
        (congrArg CommRingCat.Hom.hom ((commStructureSheaf X).obj.map_id U))).inv.app _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext W f
  change s.val W (f ≫ 𝟙 U.unop) = s.val W f
  rw [Category.comp_id]

/-- Dual restriction is functorial for composition of chart arrows. -/
theorem dualRestrict_comp (E : X.Modules) {U V W : (smallEtaleSite X)ᵒᵖ}
    (i : U ⟶ V) (j : V ⟶ W) :
    dualRestrict E (i ≫ j) = dualRestrict E i ≫
      (ModuleCat.restrictScalars ((commStructureSheaf X).obj.map i).hom).map (dualRestrict E j) ≫
        (ModuleCat.restrictScalarsComp' ((commStructureSheaf X).obj.map i).hom
          ((commStructureSheaf X).obj.map j).hom ((commStructureSheaf X).obj.map (i ≫ j)).hom
          (congrArg CommRingCat.Hom.hom ((commStructureSheaf X).obj.map_comp i j))).inv.app _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext T f
  change s.val T (f ≫ (j.unop ≫ i.unop)) = s.val T ((f ≫ j.unop) ≫ i.unop)
  rw [Category.assoc]

/-- The dual presheaf uses the actual compatible families and precomposition maps. -/
def dualPresheaf (E : X.Modules) : PresheafOfModules.{u} (commRingSheaf X).obj where
  obj := dualObj E
  map := dualRestrict E
  map_id := dualRestrict_id E
  map_comp := dualRestrict_comp E

/-- The specified families glue uniquely: the atlas inclusion is full and cover-dense,
and module morphisms descend on every slice. -/
theorem dualPresheaf_isSheaf (E : X.Modules) :
    Presheaf.IsSheaf (smallEtaleTopology X) (dualPresheaf E).presheaf := sorry

/-- The actual internal-Hom-to-structure-sheaf object on the commutative presentation. -/
def dualCommModule (E : X.Modules) : commModules X where
  val := dualPresheaf E
  isSheaf := dualPresheaf_isSheaf E

/-- The canonical dual of `E`, in the same module category as `E`. -/
def dual (E : X.Modules) : X.Modules :=
  (ofCommModules X).obj (dualCommModule E)

/-- Locally a finite free module has its finite free dual basis; these local duals
are exactly the displayed compatible-family construction. -/
instance dual_isFiniteLocallyFree (E : X.Modules) [SheafOfModules.IsFiniteLocallyFree E] :
    SheafOfModules.IsFiniteLocallyFree (dual E) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
