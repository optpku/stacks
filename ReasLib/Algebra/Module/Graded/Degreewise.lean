/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.GradedNatInt
public import ReasLib.Algebra.Module.Graded.DegreeZero.ModuleCat
public import ReasLib.CategoryTheory.InverseSystem.Positive.Cone
public import ReasLib.CategoryTheory.InverseSystem.Positive.ModuleCat.Limits

/-!
# Degreewise Systems of Internally Graded Modules

This leaf turns an integer grading on modules over a nonnegatively graded
commutative ring into modules over the degree-zero ring.  The ring grading is an
`ℤ`-submodule family, the canonical Mathlib model for an internally graded ring;
it is not a family of ideals over the ambient ring.  It also constructs
the degreewise image of an arbitrary diagram and the map induced on its limit
by a degree-preserving cone.

The ambient restriction is carried by `ModuleCat.restrictScalars`, while the canonical action on a
homogeneous piece is supplied by `GradedModule.zeroPieceModule`.  Neither a chart-dependent nor a
synthetic degree-piece instance is installed globally.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe uJ vJ uA vM

namespace GradedModule

variable {A : Type uA} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]

variable {J : Type uJ} [Category.{vJ} J]

/-- The diagram of degree-`d` pieces of a diagram of graded `A`-modules.

The indexing category is arbitrary; positive inverse systems are a later
specialization of this construction. -/
@[stacks 0EKD "degreewise graded-module diagram"]
def degreewise
    (F : J ⥤ ModuleCat.{vM} A)
    (𝒢 : ∀ j : J, ℤ → Submodule ℤ (F.obj j))
    [∀ j : J, SetLike.GradedSMul 𝒜 (𝒢 j)]
    (h𝒢 :
      ∀ ⦃i j : J⦄ (f : i ⟶ j) (d : ℤ) {x : F.obj i},
        x ∈ 𝒢 i d → F.map f x ∈ 𝒢 j d)
    (d : ℤ) :
    J ⥤ ModuleCat.{vM} (𝒜 0) where
  obj j := ModuleCat.of (𝒜 0) (𝒢 j d)
  map {i j} f :=
    ModuleCat.ofHom
      (X := 𝒢 i d)
      (Y := 𝒢 j d)
      { toFun := fun x ↦ ⟨F.map f x.1, h𝒢 f d x.2⟩
        map_add' := by
          intro x y
          apply Subtype.ext
          exact (F.map f).hom.map_add x.1 y.1
        map_smul' := by
          intro a x
          apply Subtype.ext
          change F.map f ((algebraMap (𝒜 0) A a) • x.1) =
            (algebraMap (𝒜 0) A a) • F.map f x.1
          rw [map_smul] }
  map_id := fun _ => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change F.map (𝟙 _) x.1 = x.1
    rw [F.map_id]
    rfl
  map_comp := fun f g => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change F.map (f ≫ g) x.1 = F.map g (F.map f x.1)
    rw [F.map_comp]
    rfl

/-- The morphism of the degreewise diagram acts on underlying elements through
the corresponding morphism of `F`. -/
@[simp, stacks 0EKD "degreewise diagram map evaluation"]
theorem degreewise_map_apply
    (F : J ⥤ ModuleCat.{vM} A)
    (𝒢 : ∀ j : J, ℤ → Submodule ℤ (F.obj j))
    [∀ j : J, SetLike.GradedSMul 𝒜 (𝒢 j)]
    (h𝒢 :
      ∀ ⦃i j : J⦄ (f : i ⟶ j) (d : ℤ) {x : F.obj i},
        x ∈ 𝒢 i d → F.map f x ∈ 𝒢 j d)
    (d : ℤ) {i j : J} (f : i ⟶ j)
    (x : (degreewise 𝒜 F 𝒢 h𝒢 d).obj i) :
    ((degreewise 𝒜 F 𝒢 h𝒢 d).map f x).1 = F.map f x.1 := by
  change (F.map f) x.1 = (F.map f) x.1
  rfl

/-- The inclusion of the degree-`d` stage of `degreewise` into the corresponding
ambient stage after restricting scalars to `𝒜 0`. -/
@[stacks 0EKD "degreewise stage inclusion"]
def degreewiseStageInclusion
    (F : J ⥤ ModuleCat.{vM} A)
    (𝒢 : ∀ j : J, ℤ → Submodule ℤ (F.obj j))
    [∀ j : J, SetLike.GradedSMul 𝒜 (𝒢 j)]
    (h𝒢 :
      ∀ ⦃i j : J⦄ (f : i ⟶ j) (d : ℤ) {x : F.obj i},
        x ∈ 𝒢 i d → F.map f x ∈ 𝒢 j d)
    (d : ℤ) (j : J) :
    (degreewise 𝒜 F 𝒢 h𝒢 d).obj j ⟶
      (ModuleCat.restrictScalars (algebraMap (𝒜 0) A)).obj (F.obj j) :=
  degreePieceSubtype 𝒜 (F.obj j) (𝒢 j) d

/-- The degreewise stage inclusion acts by the underlying subtype inclusion. -/
@[simp, stacks 0EKD "degreewise stage inclusion evaluation"]
theorem degreewiseStageInclusion_apply
    (F : J ⥤ ModuleCat.{vM} A)
    (𝒢 : ∀ j : J, ℤ → Submodule ℤ (F.obj j))
    [∀ j : J, SetLike.GradedSMul 𝒜 (𝒢 j)]
    (h𝒢 :
      ∀ ⦃i j : J⦄ (f : i ⟶ j) (d : ℤ) {x : F.obj i},
        x ∈ 𝒢 i d → F.map f x ∈ 𝒢 j d)
    (d : ℤ) (j : J) (x : (degreewise 𝒜 F 𝒢 h𝒢 d).obj j) :
    degreewiseStageInclusion 𝒜 F 𝒢 h𝒢 d j x = x.1 := by
  change x.1 = x.1
  rfl

/-- The stage inclusions assemble into a natural transformation from the
degreewise diagram to the ambient diagram after restriction of scalars. -/
@[stacks 0EKD "degreewise natural inclusion"]
def degreewiseInclusion
    (F : J ⥤ ModuleCat.{vM} A)
    (𝒢 : ∀ j : J, ℤ → Submodule ℤ (F.obj j))
    [∀ j : J, SetLike.GradedSMul 𝒜 (𝒢 j)]
    (h𝒢 :
      ∀ ⦃i j : J⦄ (f : i ⟶ j) (d : ℤ) {x : F.obj i},
        x ∈ 𝒢 i d → F.map f x ∈ 𝒢 j d)
    (d : ℤ) :
    degreewise 𝒜 F 𝒢 h𝒢 d ⟶
      F ⋙ ModuleCat.restrictScalars (algebraMap (𝒜 0) A) where
  app j := degreewiseStageInclusion 𝒜 F 𝒢 h𝒢 d j
  naturality := by
    intro i j f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- The `j`th component of `degreewiseInclusion` is the degree-piece subtype
map at that stage. -/
@[simp, stacks 0EKD "degreewise natural inclusion component"]
theorem degreewiseInclusion_app
    (F : J ⥤ ModuleCat.{vM} A)
    (𝒢 : ∀ j : J, ℤ → Submodule ℤ (F.obj j))
    [∀ j : J, SetLike.GradedSMul 𝒜 (𝒢 j)]
    (h𝒢 :
      ∀ ⦃i j : J⦄ (f : i ⟶ j) (d : ℤ) {x : F.obj i},
        x ∈ 𝒢 i d → F.map f x ∈ 𝒢 j d)
    (d : ℤ) (j : J) :
    (degreewiseInclusion 𝒜 F 𝒢 h𝒢 d).app j =
      degreewiseStageInclusion 𝒜 F 𝒢 h𝒢 d j := by
  rfl

/-- The degree-`d` map from the vertex of a degree-preserving cone to one
stage of the degreewise diagram. -/
@[stacks 0EKD "degreewise cone leg"]
def degreewiseConeMap
    (F : J ⥤ ModuleCat.{vM} A)
    (c : Cone F)
    (𝓜 : ℤ → Submodule ℤ c.pt)
    [SetLike.GradedSMul 𝒜 𝓜]
    (𝒢 : ∀ j : J, ℤ → Submodule ℤ (F.obj j))
    [∀ j : J, SetLike.GradedSMul 𝒜 (𝒢 j)]
    (h𝒢 :
      ∀ ⦃i j : J⦄ (f : i ⟶ j) (d : ℤ) {x : F.obj i},
        x ∈ 𝒢 i d → F.map f x ∈ 𝒢 j d)
    (h𝓜 :
      ∀ (j : J) (d : ℤ) {x : c.pt},
        x ∈ 𝓜 d → c.π.app j x ∈ 𝒢 j d)
    (d : ℤ) (j : J) :
    ModuleCat.of (𝒜 0) (𝓜 d) ⟶
      (degreewise 𝒜 F 𝒢 h𝒢 d).obj j :=
  ModuleCat.ofHom
    (X := 𝓜 d)
    (Y := 𝒢 j d)
    { toFun := fun x ↦ ⟨c.π.app j x.1, h𝓜 j d x.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact (c.π.app j).hom.map_add x.1 y.1
      map_smul' := by
        intro a x
        apply Subtype.ext
        change c.π.app j ((a : A) • x.1) = (a : A) • c.π.app j x.1
        exact (c.π.app j).hom.map_smul (a : A) x.1 }

/-- The stage map induced by a degree-preserving cone acts through the
corresponding cone leg. -/
@[simp, stacks 0EKD "degreewise cone leg evaluation"]
theorem degreewiseConeMap_apply
    (F : J ⥤ ModuleCat.{vM} A)
    (c : Cone F)
    (𝓜 : ℤ → Submodule ℤ c.pt)
    [SetLike.GradedSMul 𝒜 𝓜]
    (𝒢 : ∀ j : J, ℤ → Submodule ℤ (F.obj j))
    [∀ j : J, SetLike.GradedSMul 𝒜 (𝒢 j)]
    (h𝒢 :
      ∀ ⦃i j : J⦄ (f : i ⟶ j) (d : ℤ) {x : F.obj i},
        x ∈ 𝒢 i d → F.map f x ∈ 𝒢 j d)
    (h𝓜 :
      ∀ (j : J) (d : ℤ) {x : c.pt},
        x ∈ 𝓜 d → c.π.app j x ∈ 𝒢 j d)
    (d : ℤ) (j : J) (x : 𝓜 d) :
    degreewiseConeMap 𝒜 F c 𝓜 𝒢 h𝒢 h𝓜 d j x =
      ⟨c.π.app j x.1, h𝓜 j d x.2⟩ := by
  rfl

/-- The cone induced by a degree-preserving cone after taking one homogeneous
degree. -/
@[stacks 0EKD "degreewise cone"]
def degreewiseCone
    (F : J ⥤ ModuleCat.{vM} A)
    (c : Cone F)
    (𝓜 : ℤ → Submodule ℤ c.pt)
    [SetLike.GradedSMul 𝒜 𝓜]
    (𝒢 : ∀ j : J, ℤ → Submodule ℤ (F.obj j))
    [∀ j : J, SetLike.GradedSMul 𝒜 (𝒢 j)]
    (h𝒢 :
      ∀ ⦃i j : J⦄ (f : i ⟶ j) (d : ℤ) {x : F.obj i},
        x ∈ 𝒢 i d → F.map f x ∈ 𝒢 j d)
    (h𝓜 :
      ∀ (j : J) (d : ℤ) {x : c.pt},
        x ∈ 𝓜 d → c.π.app j x ∈ 𝒢 j d)
    (d : ℤ) :
    Cone (degreewise 𝒜 F 𝒢 h𝒢 d) where
  pt := ModuleCat.of (𝒜 0) (𝓜 d)
  π :=
    { app := fun j ↦ degreewiseConeMap 𝒜 F c 𝓜 𝒢 h𝒢 h𝓜 d j
      naturality := by
        intro i j f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        change c.π.app j x.1 = F.map f (c.π.app i x.1)
        exact (congrArg (fun φ : c.pt ⟶ F.obj j ↦ φ x.1) (c.w f)).symm }

/-- The `j`th leg of `degreewiseCone` is `degreewiseConeMap` at `j`. -/
@[simp, stacks 0EKD "degreewise cone leg projection"]
theorem degreewiseCone_π_app
    (F : J ⥤ ModuleCat.{vM} A)
    (c : Cone F)
    (𝓜 : ℤ → Submodule ℤ c.pt)
    [SetLike.GradedSMul 𝒜 𝓜]
    (𝒢 : ∀ j : J, ℤ → Submodule ℤ (F.obj j))
    [∀ j : J, SetLike.GradedSMul 𝒜 (𝒢 j)]
    (h𝒢 :
      ∀ ⦃i j : J⦄ (f : i ⟶ j) (d : ℤ) {x : F.obj i},
        x ∈ 𝒢 i d → F.map f x ∈ 𝒢 j d)
    (h𝓜 :
      ∀ (j : J) (d : ℤ) {x : c.pt},
        x ∈ 𝓜 d → c.π.app j x ∈ 𝒢 j d)
    (d : ℤ) (j : J) :
    (degreewiseCone 𝒜 F c 𝓜 𝒢 h𝒢 h𝓜 d).π.app j =
      degreewiseConeMap 𝒜 F c 𝓜 𝒢 h𝒢 h𝓜 d j := by
  rfl

/-- The canonical map from the degree-`d` piece of the vertex of a
degree-preserving cone to the limit of the degreewise diagram. -/
@[stacks 0EKD "degreewise cone limit map"]
noncomputable def degreewiseLimitMap
    (F : J ⥤ ModuleCat.{vM} A)
    (c : Cone F)
    (𝓜 : ℤ → Submodule ℤ c.pt)
    [SetLike.GradedSMul 𝒜 𝓜]
    (𝒢 : ∀ j : J, ℤ → Submodule ℤ (F.obj j))
    [∀ j : J, SetLike.GradedSMul 𝒜 (𝒢 j)]
    (h𝒢 :
      ∀ ⦃i j : J⦄ (f : i ⟶ j) (d : ℤ) {x : F.obj i},
        x ∈ 𝒢 i d → F.map f x ∈ 𝒢 j d)
    (h𝓜 :
      ∀ (j : J) (d : ℤ) {x : c.pt},
        x ∈ 𝓜 d → c.π.app j x ∈ 𝒢 j d)
    (d : ℤ) [HasLimit (degreewise 𝒜 F 𝒢 h𝒢 d)] :
    ModuleCat.of (𝒜 0) (𝓜 d) ⟶
      limit (degreewise 𝒜 F 𝒢 h𝒢 d) :=
  limit.lift (degreewise 𝒜 F 𝒢 h𝒢 d)
    (degreewiseCone 𝒜 F c 𝓜 𝒢 h𝒢 h𝓜 d)

/-- Projecting `degreewiseLimitMap` to a stage recovers the corresponding
degreewise cone stage map. -/
@[simp, reassoc, stacks 0EKD "degreewise cone limit projection"]
theorem degreewiseLimitMap_π
    (F : J ⥤ ModuleCat.{vM} A)
    (c : Cone F)
    (𝓜 : ℤ → Submodule ℤ c.pt)
    [SetLike.GradedSMul 𝒜 𝓜]
    (𝒢 : ∀ j : J, ℤ → Submodule ℤ (F.obj j))
    [∀ j : J, SetLike.GradedSMul 𝒜 (𝒢 j)]
    (h𝒢 :
      ∀ ⦃i j : J⦄ (f : i ⟶ j) (d : ℤ) {x : F.obj i},
        x ∈ 𝒢 i d → F.map f x ∈ 𝒢 j d)
    (h𝓜 :
      ∀ (j : J) (d : ℤ) {x : c.pt},
        x ∈ 𝓜 d → c.π.app j x ∈ 𝒢 j d)
    (d : ℤ) [HasLimit (degreewise 𝒜 F 𝒢 h𝒢 d)] (j : J) :
    degreewiseLimitMap 𝒜 F c 𝓜 𝒢 h𝒢 h𝓜 d ≫
        limit.π (degreewise 𝒜 F 𝒢 h𝒢 d) j =
      degreewiseConeMap 𝒜 F c 𝓜 𝒢 h𝒢 h𝓜 d j := by
  change limit.lift (degreewise 𝒜 F 𝒢 h𝒢 d)
      (degreewiseCone 𝒜 F c 𝓜 𝒢 h𝒢 h𝓜 d) ≫
      limit.π (degreewise 𝒜 F 𝒢 h𝒢 d) j = _
  rw [limit.lift_π]
  rfl

/-- The canonical inclusion from the limit of the degreewise diagram into the
ambient limit after restriction of scalars to `𝒜 0`. -/
@[stacks 0EKD "degreewise limit inclusion"]
noncomputable def degreewiseLimitInclusion
    (F : J ⥤ ModuleCat.{vM} A)
    (𝒢 : ∀ j : J, ℤ → Submodule ℤ (F.obj j))
    [∀ j : J, SetLike.GradedSMul 𝒜 (𝒢 j)]
    (h𝒢 :
      ∀ ⦃i j : J⦄ (f : i ⟶ j) (d : ℤ) {x : F.obj i},
        x ∈ 𝒢 i d → F.map f x ∈ 𝒢 j d)
    (d : ℤ)
    [HasLimit F]
    [HasLimit (degreewise 𝒜 F 𝒢 h𝒢 d)]
    [PreservesLimit F (ModuleCat.restrictScalars (algebraMap (𝒜 0) A))] :
    limit (degreewise 𝒜 F 𝒢 h𝒢 d) ⟶
      (ModuleCat.restrictScalars (algebraMap (𝒜 0) A)).obj (limit F) :=
  limit.lift (F ⋙ ModuleCat.restrictScalars (algebraMap (𝒜 0) A))
    { pt := limit (degreewise 𝒜 F 𝒢 h𝒢 d)
      π :=
        { app := fun j ↦
            limit.π (degreewise 𝒜 F 𝒢 h𝒢 d) j ≫
              degreewiseStageInclusion 𝒜 F 𝒢 h𝒢 d j
          naturality := by
            intro i j f
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro x
            exact (congrArg (fun y : 𝒢 j d ↦ (y : F.obj j))
              (ConcreteCategory.congr_hom (limit.w (degreewise 𝒜 F 𝒢 h𝒢 d) f) x)).symm } } ≫
    (preservesLimitIso (ModuleCat.restrictScalars (algebraMap (𝒜 0) A)) F).inv

/-- Projecting `degreewiseLimitInclusion` to a stage is the degreewise limit
projection followed by the stage inclusion. -/
@[simp, reassoc, stacks 0EKD "degreewise limit inclusion projection"]
theorem degreewiseLimitInclusion_π
    (F : J ⥤ ModuleCat.{vM} A)
    (𝒢 : ∀ j : J, ℤ → Submodule ℤ (F.obj j))
    [∀ j : J, SetLike.GradedSMul 𝒜 (𝒢 j)]
    (h𝒢 :
      ∀ ⦃i j : J⦄ (f : i ⟶ j) (d : ℤ) {x : F.obj i},
        x ∈ 𝒢 i d → F.map f x ∈ 𝒢 j d)
    (d : ℤ)
    [HasLimit F]
    [HasLimit (degreewise 𝒜 F 𝒢 h𝒢 d)]
    [PreservesLimit F (ModuleCat.restrictScalars (algebraMap (𝒜 0) A))]
    (j : J) :
    degreewiseLimitInclusion 𝒜 F 𝒢 h𝒢 d ≫
        (ModuleCat.restrictScalars (algebraMap (𝒜 0) A)).map (limit.π F j) =
      limit.π (degreewise 𝒜 F 𝒢 h𝒢 d) j ≫
        degreewiseStageInclusion 𝒜 F 𝒢 h𝒢 d j := by
  dsimp only [degreewiseLimitInclusion]
  rw [Category.assoc, preservesLimitIso_inv_π]
  exact limit.lift_π _ j

namespace PNat

/-- The degree-`d` positive inverse system associated to a degree-preserving
positive inverse system of graded modules. -/
@[stacks 0EKD "positive degreewise inverse system"]
abbrev degreewise
    (F : PNatInverseSystem (ModuleCat.{vM} A))
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (F.stage n))
    [gradedSMul : ∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (h𝒢 :
      ∀ {i j : ℕ+} (hij : i ≤ j) (d : ℤ) {x : F.stage j},
        x ∈ 𝒢 j d → F.transitionLinearMap hij x ∈ 𝒢 i d)
    (d : ℤ) :
    PNatInverseSystem (ModuleCat.{vM} (𝒜 0)) :=
  let 𝒢' : ∀ j : ℕ+ᵒᵈ, ℤ → Submodule ℤ (F.obj j) :=
    fun j ↦ 𝒢 (OrderDual.ofDual j)
  letI : ∀ j : ℕ+ᵒᵈ, SetLike.GradedSMul 𝒜 (𝒢' j) :=
    fun j ↦ gradedSMul (OrderDual.ofDual j)
  GradedModule.degreewise 𝒜 F 𝒢'
    (fun {i j} f e {x} hx ↦
      h𝒢
        (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f)
        e hx)
    d

/-- The stage map from the degree-`d` piece of a cone vertex to the
corresponding stage of its degreewise positive inverse system. -/
@[stacks 0EKD "positive degreewise cone leg"]
abbrev coneMap
    (F : PNatInverseSystem (ModuleCat.{vM} A))
    (s : Cone F)
    (𝓜 : ℤ → Submodule ℤ s.pt)
    [SetLike.GradedSMul 𝒜 𝓜]
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (F.stage n))
    [gradedSMul : ∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (h𝒢 :
      ∀ {i j : ℕ+} (hij : i ≤ j) (d : ℤ) {x : F.stage j},
        x ∈ 𝒢 j d → F.transitionLinearMap hij x ∈ 𝒢 i d)
    (h𝓜 :
      ∀ (n : ℕ+) (d : ℤ) {x : s.pt},
        x ∈ 𝓜 d → PNatInverseSystem.Cone.stageMap s n x ∈ 𝒢 n d)
    (d : ℤ) (n : ℕ+) :
    ModuleCat.of (𝒜 0) (𝓜 d) ⟶
      (degreewise 𝒜 F 𝒢 h𝒢 d).stage n :=
  let 𝒢' : ∀ j : ℕ+ᵒᵈ, ℤ → Submodule ℤ (F.obj j) :=
    fun j ↦ 𝒢 (OrderDual.ofDual j)
  letI : ∀ j : ℕ+ᵒᵈ, SetLike.GradedSMul 𝒜 (𝒢' j) :=
    fun j ↦ gradedSMul (OrderDual.ofDual j)
  degreewiseConeMap 𝒜 F s 𝓜 𝒢'
    (fun {i j} f e {x} hx ↦
      h𝒢
        (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f)
        e hx)
    (fun j e {x} hx ↦ h𝓜 (OrderDual.ofDual j) e hx)
    d (OrderDual.toDual n)

/-- The canonical map from the degree-`d` piece of a positive inverse-system
cone vertex to the limit of the degreewise positive inverse system. -/
@[stacks 0EKD "positive degreewise limit map"]
noncomputable def limitMap
    (F : PNatInverseSystem (ModuleCat.{vM} A))
    (s : Cone F)
    (𝓜 : ℤ → Submodule ℤ s.pt)
    [SetLike.GradedSMul 𝒜 𝓜]
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (F.stage n))
    [gradedSMul : ∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (h𝒢 :
      ∀ {i j : ℕ+} (hij : i ≤ j) (d : ℤ) {x : F.stage j},
        x ∈ 𝒢 j d → F.transitionLinearMap hij x ∈ 𝒢 i d)
    (h𝓜 :
      ∀ (n : ℕ+) (d : ℤ) {x : s.pt},
        x ∈ 𝓜 d → PNatInverseSystem.Cone.stageMap s n x ∈ 𝒢 n d)
    (d : ℤ) [HasLimit (degreewise 𝒜 F 𝒢 h𝒢 d)] :
    ModuleCat.of (𝒜 0) (𝓜 d) ⟶
      limit (degreewise 𝒜 F 𝒢 h𝒢 d) :=
  let 𝒢' : ∀ j : ℕ+ᵒᵈ, ℤ → Submodule ℤ (F.obj j) :=
    fun j ↦ 𝒢 (OrderDual.ofDual j)
  letI : ∀ j : ℕ+ᵒᵈ, SetLike.GradedSMul 𝒜 (𝒢' j) :=
    fun j ↦ gradedSMul (OrderDual.ofDual j)
  degreewiseLimitMap 𝒜 F s 𝓜 𝒢'
    (fun {i j} f e {x} hx ↦
      h𝒢
        (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f)
        e hx)
    (fun j e {x} hx ↦ h𝓜 (OrderDual.ofDual j) e hx)
    d

/-- Projecting `PNat.limitMap` to a positive stage recovers the corresponding
degreewise cone stage map. -/
@[simp, reassoc, stacks 0EKD "positive degreewise limit projection"]
theorem limitMap_π
    (F : PNatInverseSystem (ModuleCat.{vM} A))
    (s : Cone F)
    (𝓜 : ℤ → Submodule ℤ s.pt)
    [SetLike.GradedSMul 𝒜 𝓜]
    (𝒢 : ∀ n : ℕ+, ℤ → Submodule ℤ (F.stage n))
    [gradedSMul : ∀ n : ℕ+, SetLike.GradedSMul 𝒜 (𝒢 n)]
    (h𝒢 :
      ∀ {i j : ℕ+} (hij : i ≤ j) (d : ℤ) {x : F.stage j},
        x ∈ 𝒢 j d → F.transitionLinearMap hij x ∈ 𝒢 i d)
    (h𝓜 :
      ∀ (n : ℕ+) (d : ℤ) {x : s.pt},
        x ∈ 𝓜 d → PNatInverseSystem.Cone.stageMap s n x ∈ 𝒢 n d)
    (d : ℤ) [HasLimit (degreewise 𝒜 F 𝒢 h𝒢 d)] (n : ℕ+) :
    limitMap 𝒜 F s 𝓜 𝒢 h𝒢 h𝓜 d ≫
        (degreewise 𝒜 F 𝒢 h𝒢 d).limitProjection n =
      coneMap 𝒜 F s 𝓜 𝒢 h𝒢 h𝓜 d n := by
  let 𝒢' : ∀ j : ℕ+ᵒᵈ, ℤ → Submodule ℤ (F.obj j) :=
    fun j ↦ 𝒢 (OrderDual.ofDual j)
  letI : ∀ j : ℕ+ᵒᵈ, SetLike.GradedSMul 𝒜 (𝒢' j) :=
    fun j ↦ gradedSMul (OrderDual.ofDual j)
  exact degreewiseLimitMap_π 𝒜 F s 𝓜 𝒢'
    (fun {i j} f e {x} hx ↦
      h𝒢
        (show OrderDual.ofDual j ≤ OrderDual.ofDual i from leOfHom f)
        e hx)
    (fun j e {x} hx ↦ h𝓜 (OrderDual.ofDual j) e hx)
    d (OrderDual.toDual n)

end PNat

end GradedModule
