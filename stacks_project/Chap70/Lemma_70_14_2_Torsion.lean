module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Subobject
public import stacks_project.Chap67.Definition_67_14_4_IdealSubobject

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

/-- The submodule of sections of `ℱ` over `U` annihilated by `I` in the sheaf-theoretic
sense. -/
def annihilatedSections (I : IdealSubobject X) (ℱ : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) :
    Submodule ((structureSheaf X).obj.obj U) (ℱ.val.obj U) where
  carrier := {s | isAnnihilatedByIdeal I ℱ U.unop s}
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry

/-- The family of annihilator submodules is stable under étale restriction. -/
def annihilatedSubmodule (I : IdealSubobject X) (ℱ : X.Modules) :
    ℱ.val.Submodule where
  obj U := annihilatedSections I ℱ U
  map _ := sorry

/-- The subsheaf of `ℱ` consisting of sections annihilated by `I`. -/
def idealTorsionSubsheaf (I : IdealSubobject X) (ℱ : X.Modules) : X.Modules where
  val := (annihilatedSubmodule I ℱ).toPresheafOfModules
  isSheaf := sorry

/-- The canonical inclusion of the ideal-torsion subsheaf into its ambient module sheaf. -/
def idealTorsionSubsheafι (I : IdealSubobject X) (ℱ : X.Modules) :
    idealTorsionSubsheaf I ℱ ⟶ ℱ where
  val := (annihilatedSubmodule I ℱ).ι

/-- Membership in the objectwise annihilator submodule is the sheaf-theoretic condition
`I s = 0`. -/
theorem mem_annihilatedSections_iff (I : IdealSubobject X) (ℱ : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) (s : ℱ.val.obj U) :
    s ∈ annihilatedSections I ℱ U ↔ isAnnihilatedByIdeal I ℱ U.unop s :=
  sorry

/-- A section of `ℱ` over `U` lies in the ideal-torsion subsheaf if and only if it is
annihilated by `I`. -/
theorem isAnnihilatedByIdeal_iff (I : IdealSubobject X) (ℱ : X.Modules)
    (U : smallEtaleSite X) (s : ℱ.val.obj (op U)) :
    isAnnihilatedByIdeal I ℱ U s ↔
      s ∈ annihilatedSections I ℱ (op U) :=
  sorry

/-- The inclusion of the ideal-torsion subsheaf acts on sections by the underlying subtype
inclusion of the annihilator submodule. -/
theorem idealTorsionSubsheafι_app_apply (I : IdealSubobject X) (ℱ : X.Modules)
    (U : (smallEtaleSite X)ᵒᵖ) (s : (idealTorsionSubsheaf I ℱ).val.obj U) :
    ((idealTorsionSubsheafι I ℱ).val.app U s : ℱ.val.obj U) =
      Subtype.val (s : annihilatedSections I ℱ U) :=
  sorry

/-- On every étale object, the image of the torsion inclusion is the set of sections
annihilated by `I`. -/
theorem range_idealTorsionSubsheafι_app (I : IdealSubobject X) (ℱ : X.Modules)
    (U : smallEtaleSite X) :
    Set.range ((idealTorsionSubsheafι I ℱ).val.app (op U)) =
      setOf (fun s ↦ isAnnihilatedByIdeal I ℱ U s) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

