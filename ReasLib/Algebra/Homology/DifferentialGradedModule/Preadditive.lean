/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Module

/-!
# Linear Structure on Differential Graded Modules

This leaf equips right differential graded modules over a fixed cochain differential graded
algebra with their canonical preadditive and linear category structures.  The operations are
computed degreewise on the underlying linear maps.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}

private theorem hom_family_injective (M N : DifferentialGradedModule.{u, v} A) :
    Function.Injective (fun f : Hom M N ↦ f.hom) := by
  rintro ⟨f, _, _⟩ ⟨g, _, _⟩ h
  cases h
  rfl

/-- The zero morphism of right differential graded modules is zero in every degree. -/
instance instZeroHom (M N : DifferentialGradedModule.{u, v} A) : Zero (Hom M N) where
  zero :=
    { hom := fun _ ↦ 0
      comm_d n x := by simp
      comm_smul p i x a := by simp }

/-- Addition of right differential graded module morphisms is computed degreewise. -/
instance instAddHom (M N : DifferentialGradedModule.{u, v} A) : Add (Hom M N) where
  add f g :=
    { hom := fun n ↦ f.hom n + g.hom n
      comm_d n x := by
        simp only [LinearMap.add_apply, map_add, f.comm_d, g.comm_d]
      comm_smul p i x a := by
        simp only [LinearMap.add_apply, map_add, f.comm_smul, g.comm_smul] }

/-- Negation of right differential graded module morphisms is computed degreewise. -/
instance instNegHom (M N : DifferentialGradedModule.{u, v} A) : Neg (Hom M N) where
  neg f :=
    { hom := fun n ↦ -f.hom n
      comm_d n x := by
        simp only [LinearMap.neg_apply, map_neg, f.comm_d]
      comm_smul p i x a := by
        simp only [LinearMap.neg_apply, map_neg, f.comm_smul] }

/-- Subtraction of right differential graded module morphisms is computed degreewise. -/
instance instSubHom (M N : DifferentialGradedModule.{u, v} A) : Sub (Hom M N) where
  sub f g :=
    { hom := fun n ↦ f.hom n - g.hom n
      comm_d n x := by
        simp only [LinearMap.sub_apply, map_sub, f.comm_d, g.comm_d]
      comm_smul p i x a := by
        simp only [LinearMap.sub_apply, map_sub, f.comm_smul, g.comm_smul] }

/-- Natural scalar multiplication of right differential graded module morphisms is degreewise. -/
instance instNatSMulHom (M N : DifferentialGradedModule.{u, v} A) : SMul ℕ (Hom M N) where
  smul k f :=
    { hom := fun n ↦ k • f.hom n
      comm_d n x := by
        simp only [LinearMap.smul_apply, map_nsmul, f.comm_d]
      comm_smul p i x a := by
        simp only [LinearMap.smul_apply, map_nsmul, f.comm_smul] }

/-- Integer scalar multiplication of right differential graded module morphisms is degreewise. -/
instance instIntSMulHom (M N : DifferentialGradedModule.{u, v} A) : SMul ℤ (Hom M N) where
  smul k f :=
    { hom := fun n ↦ k • f.hom n
      comm_d n x := by
        simp only [LinearMap.smul_apply, map_zsmul, f.comm_d]
      comm_smul p i x a := by
        simp only [LinearMap.smul_apply, map_zsmul, f.comm_smul] }

/-- Base-ring scalar multiplication of right differential graded module morphisms is degreewise. -/
instance instSMulHom (M N : DifferentialGradedModule.{u, v} A) : SMul R (Hom M N) where
  smul r f :=
    { hom := fun n ↦ r • f.hom n
      comm_d n x := by
        simp only [LinearMap.smul_apply, map_smul, f.comm_d]
      comm_smul p i x a := by
        simp only [LinearMap.smul_apply, map_smul, f.comm_smul] }

/-- The degree-`n` component of the zero morphism is zero. -/
@[simp]
theorem zero_hom (M N : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (0 : Hom M N).hom n = 0 := rfl

/-- The degree-`n` component of a sum is the sum of the components. -/
@[simp]
theorem add_hom {M N : DifferentialGradedModule.{u, v} A} (f g : Hom M N) (n : ℤ) :
    (f + g).hom n = f.hom n + g.hom n := rfl

/-- The degree-`n` component of a negation is the negated component. -/
@[simp]
theorem neg_hom {M N : DifferentialGradedModule.{u, v} A} (f : Hom M N) (n : ℤ) :
    (-f).hom n = -f.hom n := rfl

/-- The degree-`n` component of a difference is the difference of the components. -/
@[simp]
theorem sub_hom {M N : DifferentialGradedModule.{u, v} A} (f g : Hom M N) (n : ℤ) :
    (f - g).hom n = f.hom n - g.hom n := rfl

/-- The degree-`n` component of a natural multiple is the corresponding multiple. -/
@[simp]
theorem nsmul_hom {M N : DifferentialGradedModule.{u, v} A} (k : ℕ) (f : Hom M N) (n : ℤ) :
    (k • f).hom n = k • f.hom n := rfl

/-- The degree-`n` component of an integer multiple is the corresponding multiple. -/
@[simp]
theorem zsmul_hom {M N : DifferentialGradedModule.{u, v} A} (k : ℤ) (f : Hom M N) (n : ℤ) :
    (k • f).hom n = k • f.hom n := rfl

/-- The degree-`n` component of a base-ring scalar multiple is the corresponding multiple. -/
@[simp]
theorem smul_hom {M N : DifferentialGradedModule.{u, v} A} (r : R) (f : Hom M N) (n : ℤ) :
    (r • f).hom n = r • f.hom n := rfl

/-- Morphisms of right differential graded modules form an additive commutative group. -/
@[stacks 09JI "additive structure on right DG-module morphisms"]
instance instAddCommGroupHom (M N : DifferentialGradedModule.{u, v} A) : AddCommGroup (Hom M N) :=
  Function.Injective.addCommGroup (fun f : Hom M N ↦ f.hom) (by exact hom_family_injective M N) rfl
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- Morphisms of right differential graded modules form an `R`-module. -/
@[stacks 09JI "linear structure on right DG-module morphisms"]
instance instModuleHom (M N : DifferentialGradedModule.{u, v} A) : Module R (Hom M N) :=
  Function.Injective.module R
    { toFun := fun f : Hom M N ↦ f.hom
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
    (by exact hom_family_injective M N) (fun _ _ ↦ rfl)

/-- Right differential graded modules over a fixed algebra form a preadditive category. -/
@[stacks 09JI "preadditive category of right DG modules"]
instance instPreadditive (A : CochainDGAlgebra R) :
    Preadditive (DifferentialGradedModule.{u, v} A) where
  homGroup M N := instAddCommGroupHom M N
  add_comp P Q S f f' g := by
    apply hom_family_injective P S
    funext n
    exact LinearMap.comp_add (f.hom n) (f'.hom n) (g.hom n)
  comp_add P Q S f g g' := by
    apply hom_family_injective P S
    rfl

/-- Right differential graded modules over a fixed algebra form an `R`-linear category. -/
@[stacks 09JI "linear category of right DG modules"]
instance instLinear (A : CochainDGAlgebra R) :
    Linear R (DifferentialGradedModule.{u, v} A) where
  homModule M N := instModuleHom M N
  smul_comp P Q S r f g := by
    apply hom_family_injective P S
    funext n
    exact LinearMap.comp_smul (g.hom n) r (f.hom n)
  comp_smul P Q S f r g := by
    apply hom_family_injective P S
    rfl

end DifferentialGradedModule
