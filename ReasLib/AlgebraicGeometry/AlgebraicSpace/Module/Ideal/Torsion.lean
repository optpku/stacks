/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
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
    (U : smallEtaleSite X) : isAnnihilatedByIdeal I ℱ U 0 :=
  sorry

/-- The sum of two sections annihilated by an ideal sheaf is annihilated by that ideal. -/
theorem isAnnihilatedByIdeal_add (I : IdealSubobject X) (ℱ : X.Modules)
    (U : smallEtaleSite X) {s t : ℱ.val.obj (op U)}
    (hs : isAnnihilatedByIdeal I ℱ U s) (ht : isAnnihilatedByIdeal I ℱ U t) :
    isAnnihilatedByIdeal I ℱ U (s + t) :=
  sorry

/-- A scalar multiple of a section annihilated by an ideal sheaf is annihilated by that ideal. -/
theorem isAnnihilatedByIdeal_smul (I : IdealSubobject X) (ℱ : X.Modules)
    (U : smallEtaleSite X) (a : (structureSheaf X).obj.obj (op U))
    {s : ℱ.val.obj (op U)} (hs : isAnnihilatedByIdeal I ℱ U s) :
    isAnnihilatedByIdeal I ℱ U (a • s) :=
  sorry

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
    isAnnihilatedByIdeal I ℱ V (ℱ.val.restrictₛₗ f.op s) :=
  sorry

/-- The family of annihilator submodules is stable under étale restriction. -/
def annihilatedSubmodule (I : IdealSubobject X) (ℱ : X.Modules) :
    ℱ.val.Submodule where
  obj U := annihilatedSections I ℱ U
  map f := fun s hs ↦ isAnnihilatedByIdeal_restrict I ℱ f.unop (s := s) hs

/-- The presheaf of sections annihilated by an ideal sheaf satisfies the sheaf condition. -/
theorem annihilatedSubmodule_isSheaf (I : IdealSubobject X) (ℱ : X.Modules) :
    Presheaf.IsSheaf (smallEtaleTopology X)
      (annihilatedSubmodule I ℱ).toPresheafOfModules.presheaf :=
  sorry

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
      setOf (fun s ↦ isAnnihilatedByIdeal I ℱ U s) :=
  sorry

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

