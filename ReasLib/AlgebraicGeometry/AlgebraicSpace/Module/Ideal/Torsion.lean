/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Subobject
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Affine

/-!
# Ideal torsion of étale module sheaves on algebraic spaces

The subsheaf of sections annihilated by an ideal subobject `I ⊂ 𝒪_X` is constructed
objectwise from the sheaf-theoretic condition `I s = 0` on the small étale site.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

open AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A section `s` of an `𝒪_X`-module over an étale object `U` is annihilated by an ideal
subobject `I` when every section of `I` over every étale `V ⟶ U` kills the restriction of
`s`. This is the sheaf-theoretic meaning of `I s = 0`. -/
def isAnnihilatedByIdeal (I : IdealSubobject X) (ℱ : X.Modules)
    (U : smallEtaleSite X) (s : ℱ.val.obj (op U)) : Prop :=
  ∀ (V : smallEtaleSite X) (f : V ⟶ U) (a : (I : X.Modules).val.obj (op V)),
    SheafOfModules.Subobject.inclusionApp I (op V) a • ℱ.val.restrictₛₗ f.op s = 0

/-- The zero section is annihilated by every ideal sheaf. -/
theorem isAnnihilatedByIdeal_zero (I : IdealSubobject X) (ℱ : X.Modules)
    (U : smallEtaleSite X) : isAnnihilatedByIdeal I ℱ U 0 := by
  intro V f a
  rw [map_zero, smul_zero]

/-- The sum of two sections annihilated by an ideal sheaf is annihilated by that ideal. -/
theorem isAnnihilatedByIdeal_add (I : IdealSubobject X) (ℱ : X.Modules)
    (U : smallEtaleSite X) {s t : ℱ.val.obj (op U)}
    (hs : isAnnihilatedByIdeal I ℱ U s) (ht : isAnnihilatedByIdeal I ℱ U t) :
    isAnnihilatedByIdeal I ℱ U (s + t) := by
  intro V f a
  rw [map_add]
  exact (smul_add (M := (structureSheaf X).obj.obj (op V))
    (A := ℱ.val.obj (op V)) (SheafOfModules.Subobject.inclusionApp I (op V) a)
    _ _).trans
      ((congrArg₂ (fun x y : ℱ.val.obj (op V) ↦ x + y) (hs V f a) (ht V f a)).trans
        (add_zero 0))

/-- A scalar multiple of a section annihilated by an ideal sheaf is annihilated by that ideal. -/
theorem isAnnihilatedByIdeal_smul (I : IdealSubobject X) (ℱ : X.Modules)
    (U : smallEtaleSite X) (a : (structureSheaf X).obj.obj (op U))
    {s : ℱ.val.obj (op U)} (hs : isAnnihilatedByIdeal I ℱ U s) :
    isAnnihilatedByIdeal I ℱ U (a • s) := by
  intro V f b
  letI : CommRing ((structureSheaf X).obj.obj (op V)) :=
    inferInstanceAs (CommRing Γ(V.left.left, ⊤))
  rw [map_smulₛₗ]
  exact (smul_comm (M := (structureSheaf X).obj.obj (op V))
    (N := (structureSheaf X).obj.obj (op V)) (α := ℱ.val.obj (op V))
    (SheafOfModules.Subobject.inclusionApp I (op V) b) _ _).trans
      ((congrArg (fun t : ℱ.val.obj (op V) ↦
        (structureSheaf X).obj.map f.op a • t) (hs V f b)).trans (smul_zero _))

/-- The submodule of sections of `ℱ` over `U` annihilated by `I` in the sheaf-theoretic
sense. -/
def annihilatedSections (I : IdealSubobject X) (ℱ : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) :
    Submodule ((structureSheaf X).obj.obj U) (ℱ.val.obj U) where
  carrier := {s | isAnnihilatedByIdeal I ℱ U.unop s}
  add_mem' := isAnnihilatedByIdeal_add I ℱ U.unop
  zero_mem' := isAnnihilatedByIdeal_zero I ℱ U.unop
  smul_mem' := isAnnihilatedByIdeal_smul I ℱ U.unop

/-- Étale restriction preserves annihilation by an ideal sheaf. -/
theorem isAnnihilatedByIdeal_restrict (I : IdealSubobject X) (ℱ : X.Modules)
    {U V : smallEtaleSite X} (f : V ⟶ U) {s : ℱ.val.obj (op U)}
    (hs : isAnnihilatedByIdeal I ℱ U s) :
    isAnnihilatedByIdeal I ℱ V (ℱ.val.restrictₛₗ f.op s) := by
  intro W g a
  have hcomp : ℱ.val.restrictₛₗ (g ≫ f).op s =
      ℱ.val.restrictₛₗ g.op (ℱ.val.restrictₛₗ f.op s) :=
    ℱ.val.map_comp_apply f.op g.op s
  rw [← hcomp]
  exact hs W (g ≫ f) a

/-- The family of annihilator submodules is stable under étale restriction. -/
def annihilatedSubmodule (I : IdealSubobject X) (ℱ : X.Modules) :
    ℱ.val.Submodule where
  obj U := annihilatedSections I ℱ U
  map f := fun s hs ↦ isAnnihilatedByIdeal_restrict I ℱ f.unop (s := s) hs

/-- The presheaf of sections annihilated by an ideal sheaf satisfies the sheaf condition. -/
theorem annihilatedSubmodule_isSheaf (I : IdealSubobject X) (ℱ : X.Modules) :
    Presheaf.IsSheaf (smallEtaleTopology X)
      (annihilatedSubmodule I ℱ).toPresheafOfModules.presheaf := by
  let F := ℱ.val.presheaf ⋙ forget AddCommGrpCat.{u}
  let T : Subfunctor F :=
    { obj U := (annihilatedSections I ℱ U : Set (ℱ.val.obj U))
      map f := fun _ hs ↦ (annihilatedSubmodule I ℱ).map f hs }
  have hF : Presieve.IsSheaf (smallEtaleTopology X) F :=
    Presieve.isSheaf_iso _
      (Functor.isoWhiskerLeft ℱ.val.presheaf AddCommGrpCat.coyonedaObjIsoForget)
      (ℱ.isSheaf (AddCommGrpCat.of (ULift.{u} ℤ)))
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{u})
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  change Presieve.IsSheaf (smallEtaleTopology X) T.toFunctor
  apply (T.isSheaf_iff hF).mpr
  intro U s hs V f a
  apply (hF _ ((smallEtaleTopology X).pullback_stable f hs)).isSeparatedFor.ext
  intro W g hg
  change isAnnihilatedByIdeal I ℱ W (ℱ.val.restrictₛₗ (g ≫ f).op s) at hg
  let b := (I : X.Modules).val.restrictₛₗ g.op a
  have hid : ℱ.val.restrictₛₗ (𝟙 W).op (ℱ.val.restrictₛₗ (g ≫ f).op s) =
      ℱ.val.restrictₛₗ (g ≫ f).op s :=
    ConcreteCategory.congr_hom (ℱ.val.presheaf.map_id (op W)) _
  have hz : (SheafOfModules.Subobject.inclusionApp I (op W) b :
      (structureSheaf X).obj.obj (op W)) • ℱ.val.restrictₛₗ (g ≫ f).op s = 0 :=
    (congrArg (fun t : ℱ.val.obj (op W) ↦
      (SheafOfModules.Subobject.inclusionApp I (op W) b :
        (structureSheaf X).obj.obj (op W)) • t) hid.symm).trans (hg W (𝟙 W) b)
  have hnat : (structureSheaf X).obj.map g.op
      (SheafOfModules.Subobject.inclusionApp I (op V) a) =
      SheafOfModules.Subobject.inclusionApp I (op W) b :=
    (PresheafOfModules.naturality_apply I.arrow.val g.op a).symm
  have hcomp : ℱ.val.restrictₛₗ g.op (ℱ.val.restrictₛₗ f.op s) =
      ℱ.val.restrictₛₗ (g ≫ f).op s :=
    (ℱ.val.map_comp_apply f.op g.op s).symm
  calc
    ℱ.val.restrictₛₗ g.op
        ((SheafOfModules.Subobject.inclusionApp I (op V) a :
          (structureSheaf X).obj.obj (op V)) • ℱ.val.restrictₛₗ f.op s) =
        (structureSheaf X).obj.map g.op
          (SheafOfModules.Subobject.inclusionApp I (op V) a) •
            ℱ.val.restrictₛₗ g.op (ℱ.val.restrictₛₗ f.op s) :=
      (ℱ.val.restrictₛₗ g.op).map_smulₛₗ _ _
    _ = (SheafOfModules.Subobject.inclusionApp I (op W) b :
        (structureSheaf X).obj.obj (op W)) • ℱ.val.restrictₛₗ (g ≫ f).op s :=
      congrArg₂ (fun (r : (structureSheaf X).obj.obj (op W))
        (t : ℱ.val.obj (op W)) ↦ r • t) hnat hcomp
    _ = 0 := hz
    _ = ℱ.val.restrictₛₗ g.op 0 := ((ℱ.val.restrictₛₗ g.op).map_zero).symm

/-- The subsheaf of `ℱ` consisting of sections annihilated by `I`. -/
def idealTorsionSubsheaf (I : IdealSubobject X) (ℱ : X.Modules) : X.Modules where
  val := (annihilatedSubmodule I ℱ).toPresheafOfModules
  isSheaf := annihilatedSubmodule_isSheaf I ℱ

/-- The canonical inclusion of the ideal-torsion subsheaf into its ambient module sheaf. -/
def idealTorsionSubsheafι (I : IdealSubobject X) (ℱ : X.Modules) :
    idealTorsionSubsheaf I ℱ ⟶ ℱ where
  val := (annihilatedSubmodule I ℱ).ι

/-- Membership in the objectwise annihilator submodule is the sheaf-theoretic condition
`I s = 0`. -/
theorem mem_annihilatedSections_iff (I : IdealSubobject X) (ℱ : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) (s : ℱ.val.obj U) :
    s ∈ annihilatedSections I ℱ U ↔ isAnnihilatedByIdeal I ℱ U.unop s :=
  Iff.rfl

/-- The inclusion of the ideal-torsion subsheaf acts on sections by the underlying subtype
inclusion of the annihilator submodule. -/
theorem idealTorsionSubsheafι_app_apply (I : IdealSubobject X) (ℱ : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) (s : (idealTorsionSubsheaf I ℱ).val.obj U) :
    ((idealTorsionSubsheafι I ℱ).val.app U s : ℱ.val.obj U) =
      Subtype.val (s : annihilatedSections I ℱ U) :=
  rfl

/-- On every étale object, the image of the torsion inclusion is the set of sections
annihilated by `I`. -/
theorem range_idealTorsionSubsheafι_app (I : IdealSubobject X) (ℱ : X.Modules)
    (U : smallEtaleSite X) :
    Set.range ((idealTorsionSubsheafι I ℱ).val.app (op U)) =
      setOf (fun s ↦ isAnnihilatedByIdeal I ℱ U s) := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact t.property
  · intro hs
    exact ⟨⟨s, hs⟩, rfl⟩

/-- The subsheaf annihilated by a quasi-coherent finite type ideal of an algebraic space
is quasi-coherent when the ambient module is quasi-coherent. -/
instance idealTorsionSubsheaf_isQuasicoherent (I : IdealSubobject X) (ℱ : X.Modules)
    [(I : X.Modules).IsQuasicoherent] [(I : X.Modules).IsFiniteType] [ℱ.IsQuasicoherent] :
    (idealTorsionSubsheaf I ℱ).IsQuasicoherent :=
  sorry

/-- On an affine étale object, the image of the torsion inclusion consists exactly of
sections annihilated by the sections of the quasi-coherent finite type ideal. -/
theorem range_idealTorsionSubsheafι_app_eq_affine_annihilatedSections
    (I : IdealSubobject X) (ℱ : X.Modules)
    [(I : X.Modules).IsQuasicoherent] [(I : X.Modules).IsFiniteType] [ℱ.IsQuasicoherent]
    (U : affineEtaleSite X) :
    Set.range ((idealTorsionSubsheafι I ℱ).val.app (op U.obj)) =
      setOf (fun s ↦ ∀ a, a ∈ SheafOfModules.Subobject.sections I (op U.obj) → a • s = 0) :=
  sorry

/-- A stalk section is annihilated by `I` when every representative over an étale neighborhood
is killed, as a germ, by every section of `I` over that neighborhood. -/
def isAnnihilatedByIdealStalk (I : IdealSubobject X) (ℱ : X.Modules)
    (xbar : GeometricPoint X) (s : stalk xbar ℱ) : Prop :=
  ∀ (N : GeometricPoint.SmallEtaleNeighborhood xbar)
    (a : (I : X.Modules).val.obj (op N.toSite)) (σ : ℱ.val.obj (op N.toSite)),
    toStalk xbar N σ = s →
      stalkSMul xbar N (SheafOfModules.Subobject.inclusionApp I (op N.toSite) a) σ =
        toStalk xbar N 0

/-- At a geometric point, the image of the torsion stalk inclusion consists exactly of
stalk sections annihilated by every germ of the quasi-coherent finite type ideal. -/
theorem range_idealTorsionSubsheafι_stalk_eq_annihilatedStalkSections
    (I : IdealSubobject X) (ℱ : X.Modules)
    [(I : X.Modules).IsQuasicoherent] [(I : X.Modules).IsFiniteType] [ℱ.IsQuasicoherent]
    (xbar : GeometricPoint X) :
    Set.range (stalkMap xbar (idealTorsionSubsheafι I ℱ)) =
      setOf (isAnnihilatedByIdealStalk I ℱ xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

