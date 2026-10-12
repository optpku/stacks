/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/-- The zero morphism of right differential graded modules is zero in every degree. -/
instance instZeroHom (M N : DifferentialGradedModule.{u, v} A) : Zero (Hom M N) where
  zero :=
    { hom := fun _ ↦ 0
      comm_d := sorry
      comm_smul := sorry }

/-- Addition of right differential graded module morphisms is computed degreewise. -/
instance instAddHom (M N : DifferentialGradedModule.{u, v} A) : Add (Hom M N) where
  add f g :=
    { hom := fun n ↦ f.hom n + g.hom n
      comm_d := sorry
      comm_smul := sorry }

/-- Negation of right differential graded module morphisms is computed degreewise. -/
instance instNegHom (M N : DifferentialGradedModule.{u, v} A) : Neg (Hom M N) where
  neg f :=
    { hom := fun n ↦ -f.hom n
      comm_d := sorry
      comm_smul := sorry }

/-- Subtraction of right differential graded module morphisms is computed degreewise. -/
instance instSubHom (M N : DifferentialGradedModule.{u, v} A) : Sub (Hom M N) where
  sub f g :=
    { hom := fun n ↦ f.hom n - g.hom n
      comm_d := sorry
      comm_smul := sorry }

/-- Natural scalar multiplication of right differential graded module morphisms is degreewise. -/
instance instNatSMulHom (M N : DifferentialGradedModule.{u, v} A) : SMul ℕ (Hom M N) where
  smul k f :=
    { hom := fun n ↦ k • f.hom n
      comm_d := sorry
      comm_smul := sorry }

/-- Integer scalar multiplication of right differential graded module morphisms is degreewise. -/
instance instIntSMulHom (M N : DifferentialGradedModule.{u, v} A) : SMul ℤ (Hom M N) where
  smul k f :=
    { hom := fun n ↦ k • f.hom n
      comm_d := sorry
      comm_smul := sorry }

/-- Base-ring scalar multiplication of right differential graded module morphisms is degreewise. -/
instance instSMulHom (M N : DifferentialGradedModule.{u, v} A) : SMul R (Hom M N) where
  smul r f :=
    { hom := fun n ↦ r • f.hom n
      comm_d := sorry
      comm_smul := sorry }

/-- The degree-`n` component of the zero morphism is zero. -/
@[simp]
theorem zero_hom (M N : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    (0 : Hom M N).hom n = 0 := sorry

/-- The degree-`n` component of a sum is the sum of the components. -/
@[simp]
theorem add_hom {M N : DifferentialGradedModule.{u, v} A} (f g : Hom M N) (n : ℤ) :
    (f + g).hom n = f.hom n + g.hom n := sorry

/-- The degree-`n` component of a negation is the negated component. -/
@[simp]
theorem neg_hom {M N : DifferentialGradedModule.{u, v} A} (f : Hom M N) (n : ℤ) :
    (-f).hom n = -f.hom n := sorry

/-- The degree-`n` component of a difference is the difference of the components. -/
@[simp]
theorem sub_hom {M N : DifferentialGradedModule.{u, v} A} (f g : Hom M N) (n : ℤ) :
    (f - g).hom n = f.hom n - g.hom n := sorry

/-- The degree-`n` component of a natural multiple is the corresponding multiple. -/
@[simp]
theorem nsmul_hom {M N : DifferentialGradedModule.{u, v} A} (k : ℕ) (f : Hom M N) (n : ℤ) :
    (k • f).hom n = k • f.hom n := sorry

/-- The degree-`n` component of an integer multiple is the corresponding multiple. -/
@[simp]
theorem zsmul_hom {M N : DifferentialGradedModule.{u, v} A} (k : ℤ) (f : Hom M N) (n : ℤ) :
    (k • f).hom n = k • f.hom n := sorry

/-- The degree-`n` component of a base-ring scalar multiple is the corresponding multiple. -/
@[simp]
theorem smul_hom {M N : DifferentialGradedModule.{u, v} A} (r : R) (f : Hom M N) (n : ℤ) :
    (r • f).hom n = r • f.hom n := sorry

/-- Morphisms of right differential graded modules form an additive commutative group. -/
@[stacks 09JI "additive structure on right DG-module morphisms"]
instance instAddCommGroupHom (M N : DifferentialGradedModule.{u, v} A) : AddCommGroup (Hom M N) :=
  Function.Injective.addCommGroup (fun f : Hom M N ↦ f.hom) sorry sorry
    (fun _ _ ↦ sorry) (fun _ ↦ sorry) (fun _ _ ↦ sorry)
      (fun _ _ ↦ sorry) (fun _ _ ↦ sorry)

/-- Morphisms of right differential graded modules form an `R`-module. -/
@[stacks 09JI "linear structure on right DG-module morphisms"]
instance instModuleHom (M N : DifferentialGradedModule.{u, v} A) : Module R (Hom M N) :=
  Function.Injective.module R
    { toFun := fun f : Hom M N ↦ f.hom
      map_zero' := sorry
      map_add' := sorry }
    sorry (fun _ _ ↦ sorry)

/-- Right differential graded modules over a fixed algebra form a preadditive category. -/
@[stacks 09JI "preadditive category of right DG modules"]
instance instPreadditive (A : CochainDGAlgebra R) :
    Preadditive (DifferentialGradedModule.{u, v} A) where
  homGroup M N := instAddCommGroupHom M N
  add_comp := sorry
  comp_add := sorry

/-- Right differential graded modules over a fixed algebra form an `R`-linear category. -/
@[stacks 09JI "linear category of right DG modules"]
instance instLinear (A : CochainDGAlgebra R) :
    Linear R (DifferentialGradedModule.{u, v} A) where
  homModule M N := instModuleHom M N
  smul_comp := sorry
  comp_smul := sorry

end DifferentialGradedModule
