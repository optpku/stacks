/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.BaseChange
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BaseChange
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Formal
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.OfModule
import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-Zero Sections of Formal Gluing Data

The degree-zero module of a formal gluing object is the kernel of the
difference between its global-to-local maps and its glued-source-to-local
maps.  The target local modules are restricted along the source path through
`Localization.awayMap`; the canonical restriction-of-scalars square compares
that path with the target-ring path used by the global module.

@stack 05EL
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v w

noncomputable section

namespace LocalizedModule.Away.FormalGluing

variable {R S : Type u} [CommRing R] [CommRing S]
variable {ι : Type w} {φ : R →+* S} {f : ι → R}

/-- The source of the degree-zero compatibility map: the target-ring global
module, restricted to `R`, together with the module of compatible source
local sections. -/
@[stacks 05EL "formal gluing degree-zero comparison source"]
noncomputable abbrev h0Source
    (X : FormalGluing.{u, v, w} φ f) :=
  ((ModuleCat.restrictScalars φ).obj X.globalModule) ×
    X.sourceGluing.gluedModule

/-- The `i`-th target local module used by the degree-zero comparison,
restricted first along `Localization.awayMap φ (f i)` and then to `R`.
Choosing the source path makes the local unit canonical; the global path is
transported to it by `baseChangeRestrictScalarsIso`. -/
@[stacks 05EL "formal gluing degree-zero local target"]
noncomputable abbrev h0LocalTarget
    (X : FormalGluing.{u, v, w} φ f) (i : ι) :=
  (ModuleCat.restrictScalars
    (algebraMap R (Localization.Away (f i)))).obj
      ((ModuleCat.restrictScalars
        (Localization.awayMap φ (f i))).obj
          ((X.sourceGluing.baseChange φ).localModule i))

/-- The global contribution to the `i`-th degree-zero comparison.  It
localizes the target module, applies the formal-gluing comparison, and then
uses the scalar-restriction square to reach `h0LocalTarget`. -/
@[stacks 05EL "formal gluing degree-zero global local map"]
noncomputable def h0GlobalLocalMap
    (X : FormalGluing.{u, v, w} φ f) (i : ι) :
    ((ModuleCat.restrictScalars φ).obj X.globalModule) →ₗ[R]
      X.h0LocalTarget i :=
  ((ModuleCat.restrictScalars φ).map
      (Gluing.ofModuleProjection (fun j ↦ φ (f j))
          X.globalModule i ≫
        (ModuleCat.restrictScalars
          (algebraMap S (Localization.Away (φ (f i))))).map
            (X.comparisonIso.hom.hom i)) ≫
    (Localization.Away.baseChangeRestrictScalarsIso φ (f i)
      ((X.sourceGluing.baseChange φ).localModule i)).hom).hom

/-- The source-gluing contribution to the `i`-th degree-zero comparison.
It projects a compatible source family to its `i`-th local section and then
applies the local base-change unit. -/
@[stacks 05EL "formal gluing degree-zero glued local map"]
noncomputable def h0GluedLocalMap
    (X : FormalGluing.{u, v, w} φ f) (i : ι) :
    X.sourceGluing.gluedModule →ₗ[R] X.h0LocalTarget i :=
  ((X.sourceGluing.toPreGluing.baseChangeUnit φ i).hom.restrictScalars R).comp
    (X.sourceGluing.projection i)

/-- The `i`-th degree-zero compatibility component is the difference between
the global and source-gluing local sections. -/
@[stacks 05EL "formal gluing degree-zero compatibility component"]
noncomputable def h0ComparisonComponent
    (X : FormalGluing.{u, v, w} φ f) (i : ι) :
    X.h0Source →ₗ[R] X.h0LocalTarget i :=
  (X.h0GlobalLocalMap i).comp
      (LinearMap.fst R
        ((ModuleCat.restrictScalars φ).obj X.globalModule)
        X.sourceGluing.gluedModule) -
    (X.h0GluedLocalMap i).comp
      (LinearMap.snd R
        ((ModuleCat.restrictScalars φ).obj X.globalModule)
        X.sourceGluing.gluedModule)

/-- The family of target local modules receiving the degree-zero
compatibility map. -/
@[stacks 05EL "formal gluing degree-zero comparison target"]
noncomputable abbrev h0Target
    (X : FormalGluing.{u, v, w} φ f) :=
  ∀ i : ι, X.h0LocalTarget i

/-- The degree-zero compatibility map of a formal gluing object, assembled
from its local comparison components. -/
@[stacks 05EL "formal gluing degree-zero compatibility map"]
noncomputable def h0CompatibilityMap
    (X : FormalGluing.{u, v, w} φ f) :
    X.h0Source →ₗ[R] X.h0Target :=
  LinearMap.pi fun i ↦ X.h0ComparisonComponent i

/-- Evaluating the degree-zero compatibility map at `i` gives the `i`-th
comparison component. -/
@[simp, stacks 05EL "formal gluing degree-zero compatibility evaluation"]
theorem h0CompatibilityMap_apply
    (X : FormalGluing.{u, v, w} φ f) (x : X.h0Source) (i : ι) :
    X.h0CompatibilityMap x i = X.h0ComparisonComponent i x := by
  rfl

/-- The degree-zero module of a formal gluing object is the kernel of its
global-versus-local compatibility map. -/
@[stacks 05EL "formal gluing degree-zero module"]
noncomputable def h0Module
    (X : FormalGluing.{u, v, w} φ f) :
    Submodule R X.h0Source :=
  LinearMap.ker X.h0CompatibilityMap

/-- A pair belongs to the degree-zero module exactly when its global and
source-gluing sections agree in every base-changed local target. -/
@[stacks 05EL "formal gluing degree-zero module membership"]
theorem mem_h0Module_iff
    (X : FormalGluing.{u, v, w} φ f) (x : X.h0Source) :
    x ∈ X.h0Module ↔
      ∀ i : ι, X.h0GlobalLocalMap i x.1 =
        X.h0GluedLocalMap i x.2 := by
  change X.h0CompatibilityMap x = 0 ↔ _
  constructor
  · intro hx i
    have hi := congrFun hx i
    change X.h0GlobalLocalMap i x.1 - X.h0GluedLocalMap i x.2 = 0 at hi
    exact sub_eq_zero.mp hi
  · intro hx
    funext i
    change X.h0GlobalLocalMap i x.1 - X.h0GluedLocalMap i x.2 = 0
    exact sub_eq_zero.mpr (hx i)

/-- The bundled source-ring module underlying degree-zero formal-gluing
sections.  Bundling occurs only after taking the kernel, so local comparison
maps may retain their natural smaller universes. -/
@[stacks 05EL "formal gluing bundled degree-zero module"]
noncomputable abbrev h0Object
    (X : FormalGluing.{u, v, w} φ f) :
    ModuleCat.{max u v w} R :=
  ModuleCat.of R X.h0Module

/-- The map on the ambient degree-zero comparison sources induced by a
morphism of formal gluing objects. -/
@[stacks 05EL "formal gluing degree-zero ambient map"]
noncomputable def h0UnderlyingMap
    {X Y : FormalGluing.{u, v, w} φ f} (α : X ⟶ Y) :
    X.h0Source →ₗ[R] Y.h0Source :=
  LinearMap.prodMap
    ((ModuleCat.restrictScalars φ).map α.globalMap).hom
    α.sourceMap.gluedMap

/-- The map between the `i`-th local targets induced by a morphism of formal
gluing objects. -/
@[stacks 05EL "formal gluing degree-zero local target map"]
noncomputable def h0LocalTargetMap
    {X Y : FormalGluing.{u, v, w} φ f} (α : X ⟶ Y) (i : ι) :
    X.h0LocalTarget i →ₗ[R] Y.h0LocalTarget i :=
  ((ModuleCat.restrictScalars
    (algebraMap R (Localization.Away (f i)))).map <|
      (ModuleCat.restrictScalars
        (Localization.awayMap φ (f i))).map
          ((Gluing.baseChangeMap φ α.sourceMap).hom i)).hom

/-- The coordinatewise map between the families of local targets. -/
@[stacks 05EL "formal gluing degree-zero target-family map"]
noncomputable def h0TargetMap
    {X Y : FormalGluing.{u, v, w} φ f} (α : X ⟶ Y) :
    X.h0Target →ₗ[R] Y.h0Target :=
  LinearMap.piMap fun i ↦ h0LocalTargetMap α i

/-- Each local degree-zero comparison component is natural in morphisms of
formal gluing objects. -/
@[stacks 05EL "formal gluing degree-zero component naturality"]
theorem h0ComparisonComponent_naturality
    {X Y : FormalGluing.{u, v, w} φ f} (α : X ⟶ Y) (i : ι) :
    (Y.h0ComparisonComponent i).comp (h0UnderlyingMap α) =
      (h0LocalTargetMap α i).comp (X.h0ComparisonComponent i) := by
  apply LinearMap.ext
  intro x
  change Y.h0GlobalLocalMap i (α.globalMap x.1) -
      Y.h0GluedLocalMap i (α.sourceMap.gluedMap x.2) =
    h0LocalTargetMap α i
      (X.h0GlobalLocalMap i x.1 - X.h0GluedLocalMap i x.2)
  rw [map_sub]
  congr 1
  · have hprojection := congrArg (fun g ↦ g x.1)
      (Gluing.ofModuleProjection_naturality (fun j ↦ φ (f j)) α.globalMap i)
    have hcomparison := congrArg
      (fun g ↦ g.hom i (Gluing.ofModuleProjection
        (fun j ↦ φ (f j)) X.globalModule i x.1)) α.comm.w
    change Gluing.ofModuleProjection (fun j ↦ φ (f j)) Y.globalModule i
        (α.globalMap x.1) =
      (Gluing.ofModuleMap (fun j ↦ φ (f j)) α.globalMap).hom i
        (Gluing.ofModuleProjection (fun j ↦ φ (f j)) X.globalModule i x.1)
      at hprojection
    change Y.comparisonIso.hom.hom i
        ((Gluing.ofModuleMap (fun j ↦ φ (f j)) α.globalMap).hom i
          (Gluing.ofModuleProjection (fun j ↦ φ (f j)) X.globalModule i x.1)) =
      (Gluing.baseChangeMap φ α.sourceMap).hom i
        (X.comparisonIso.hom.hom i
          (Gluing.ofModuleProjection (fun j ↦ φ (f j)) X.globalModule i x.1))
      at hcomparison
    change Y.comparisonIso.hom.hom i
        (Gluing.ofModuleProjection (fun j ↦ φ (f j)) Y.globalModule i
          (α.globalMap x.1)) =
      (Gluing.baseChangeMap φ α.sourceMap).hom i
        (X.comparisonIso.hom.hom i
          (Gluing.ofModuleProjection (fun j ↦ φ (f j)) X.globalModule i x.1))
    rw [hprojection]
    exact hcomparison
  · exact congrArg (fun g ↦ g (X.sourceGluing.projection i x.2))
      (Gluing.baseChangeUnit_naturality φ α.sourceMap i)

/-- The assembled degree-zero compatibility map is natural in formal-gluing
morphisms. -/
@[stacks 05EL "formal gluing degree-zero compatibility naturality"]
theorem h0CompatibilityMap_naturality
    {X Y : FormalGluing.{u, v, w} φ f} (α : X ⟶ Y) :
    Y.h0CompatibilityMap.comp (h0UnderlyingMap α) =
      (h0TargetMap α).comp X.h0CompatibilityMap := by
  apply LinearMap.ext
  intro x
  funext i
  exact DFunLike.congr_fun (h0ComparisonComponent_naturality α i) x

/-- The ambient degree-zero map sends the source kernel into the target
kernel. -/
@[stacks 05EL "formal gluing degree-zero map preserves compatibility"]
theorem h0Map_mem
    {X Y : FormalGluing.{u, v, w} φ f}
    (α : X ⟶ Y) (x : X.h0Module) :
    h0UnderlyingMap α x.1 ∈ Y.h0Module := by
  change Y.h0CompatibilityMap (h0UnderlyingMap α x.1) = 0
  have hx : X.h0CompatibilityMap x.1 = 0 := x.2
  have h := DFunLike.congr_fun (h0CompatibilityMap_naturality α) x.1
  simpa only [LinearMap.comp_apply, hx, map_zero] using h

/-- The map on degree-zero modules induced by a morphism of formal gluing
objects.  Its carrier map is explicit; only preservation of the kernel is a
propositional proof field. -/
@[stacks 05EL "formal gluing degree-zero induced map"]
noncomputable def h0Map
    {X Y : FormalGluing.{u, v, w} φ f}
    (α : X ⟶ Y) : X.h0Module →ₗ[R] Y.h0Module :=
  LinearMap.codRestrict Y.h0Module
    ((h0UnderlyingMap α).domRestrict X.h0Module)
    (h0Map_mem α)

/-- The induced degree-zero map has the ambient componentwise map as its
underlying function. -/
@[simp, stacks 05EL "formal gluing degree-zero induced map application"]
theorem h0Map_apply
    {X Y : FormalGluing.{u, v, w} φ f}
    (α : X ⟶ Y) (x : X.h0Module) :
    (h0Map α x).1 = h0UnderlyingMap α x.1 := by
  rfl

/-- The degree-zero construction sends identity morphisms to identity module
morphisms. -/
@[stacks 05EL "formal gluing degree-zero identity"]
theorem h0Map_id (X : FormalGluing.{u, v, w} φ f) :
    ModuleCat.ofHom (X := X.h0Object) (Y := X.h0Object)
        (h0Map (𝟙 X : X ⟶ X)) =
      𝟙 X.h0Object := by
  rfl

/-- The degree-zero construction sends composites to composites. -/
@[stacks 05EL "formal gluing degree-zero composition"]
theorem h0Map_comp
    {X Y Z : FormalGluing.{u, v, w} φ f}
    (α : X ⟶ Y) (β : Y ⟶ Z) :
    ModuleCat.ofHom (X := X.h0Object) (Y := Z.h0Object)
        (h0Map (α ≫ β)) =
      ModuleCat.ofHom (X := X.h0Object) (Y := Y.h0Object) (h0Map α) ≫
        ModuleCat.ofHom (X := Y.h0Object) (Y := Z.h0Object) (h0Map β) := by
  rfl

/-- The degree-zero formal-gluing functor to source-ring modules. -/
@[stacks 05EL "formal gluing degree-zero functor"]
noncomputable def h0Functor :
    FormalGluing.{u, v, w} φ f ⥤ ModuleCat.{max u v w} R where
  obj X := X.h0Object
  map α := ModuleCat.ofHom (h0Map α)
  map_id := h0Map_id
  map_comp := h0Map_comp

end LocalizedModule.Away.FormalGluing
