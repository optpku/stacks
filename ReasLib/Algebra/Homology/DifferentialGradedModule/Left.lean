/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Module

/-!
# Left Differential Graded Modules

This leaf owns left modules over a cochain differential graded algebra and their ordinary
category.  The conversion to right modules over the opposite algebra lives in the separate
`Opposite` leaf.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

variable {R : Type u} [CommRing R]

namespace LeftDifferentialGradedModule

/-- The degree-zero left action on `M^p` has target `M^(0 + p)`. -/
theorem zeroActionTarget {M : ℤ → ModuleCat.{v} R} (p : ℤ) :
    (M p : Type v) = M (0 + p) := sorry

/-- Two successive homogeneous left actions have target `M^((i + j) + p)`. -/
theorem mulActionTarget {M : ℤ → ModuleCat.{v} R} (p i j : ℤ) :
    (M (i + (j + p)) : Type v) = M ((i + j) + p) := sorry

/-- The first left Leibniz summand has target `M^(i + p + 1)`. -/
theorem dLeftActionTarget {M : ℤ → ModuleCat.{v} R} (p i : ℤ) :
    (M ((i + 1) + p) : Type v) = M (i + p + 1) := sorry

/-- The second left Leibniz summand has target `M^(i + p + 1)`. -/
theorem dRightActionTarget {M : ℤ → ModuleCat.{v} R} (p i : ℤ) :
    (M (i + (p + 1)) : Type v) = M (i + p + 1) := sorry

end LeftDifferentialGradedModule

/-- A left differential graded module over a cochain differential graded algebra. -/
@[stacks 0FPZ "left differential graded module"]
structure LeftDifferentialGradedModule (A : CochainDGAlgebra R) where
  /-- The degree-`n` module. -/
  X : ℤ → ModuleCat.{v} R
  /-- The degree-raising differential. -/
  d (n : ℤ) : X n →ₗ[R] X (n + 1)
  /-- The homogeneous left action. -/
  smul (i p : ℤ) : A.X i →ₗ[R] X p →ₗ[R] X (i + p)
  /-- The differential squares to zero. -/
  d_sq (n : ℤ) (x : X n) : d (n + 1) (d n x) = 0
  /-- The degree-zero unit acts by scalar multiplication. -/
  smul_one (r : R) (p : ℤ) (x : X p) :
    smul 0 p (r • A.one) x = cast (LeftDifferentialGradedModule.zeroActionTarget p) (r • x)
  /-- Multiplication in the algebra acts by successive left actions. -/
  smul_mul (i j p : ℤ) (a : A.X i) (b : A.X j) (x : X p) :
    smul (i + j) p (A.mul i j a b) x =
      cast (LeftDifferentialGradedModule.mulActionTarget p i j)
        (smul i (j + p) a (smul j p b x))
  /-- The differential satisfies the graded Leibniz rule for the left action. -/
  comm_d (i p : ℤ) (a : A.X i) (x : X p) :
    d (i + p) (smul i p a x) =
      cast (LeftDifferentialGradedModule.dLeftActionTarget p i)
          (smul (i + 1) p (A.d i a) x) +
        (i.negOnePow : R) •
          cast (LeftDifferentialGradedModule.dRightActionTarget p i)
            (smul i (p + 1) a (d p x))

namespace LeftDifferentialGradedModule

variable {A : CochainDGAlgebra R}

/-- Applying the differential twice to a homogeneous element gives zero. -/
theorem d_sq_apply (M : LeftDifferentialGradedModule A) (n : ℤ) (x : M.X n) :
    M.d (n + 1) (M.d n x) = 0 := sorry

/-- A morphism of left differential graded modules. -/
@[stacks 0FPZ "morphism of left differential graded modules"]
structure Hom (M : LeftDifferentialGradedModule.{u, v} A)
    (N : LeftDifferentialGradedModule.{u, w} A) where
  /-- The degree-preserving linear components. -/
  hom (n : ℤ) : M.X n →ₗ[R] N.X n
  /-- Compatibility with the differential. -/
  comm_d (n : ℤ) (x : M.X n) : hom (n + 1) (M.d n x) = N.d n (hom n x)
  /-- Compatibility with the left action. -/
  comm_smul (i p : ℤ) (a : A.X i) (x : M.X p) :
    hom (i + p) (M.smul i p a x) = N.smul i p a (hom p x)

namespace Hom

/-- The identity morphism commutes with the differential. -/
theorem id_comm_d (M : LeftDifferentialGradedModule A) (n : ℤ) (x : M.X n) :
    (LinearMap.id : M.X (n + 1) →ₗ[R] M.X (n + 1)) (M.d n x) =
      M.d n ((LinearMap.id : M.X n →ₗ[R] M.X n) x) := sorry

/-- The identity morphism commutes with the left action. -/
theorem id_comm_smul (M : LeftDifferentialGradedModule A)
    (i p : ℤ) (a : A.X i) (x : M.X p) :
    (LinearMap.id : M.X (i + p) →ₗ[R] M.X (i + p)) (M.smul i p a x) =
      M.smul i p a ((LinearMap.id : M.X p →ₗ[R] M.X p) x) := sorry

/-- The identity left-DG-module morphism. -/
def id (M : LeftDifferentialGradedModule A) : Hom M M where
  hom _ := LinearMap.id
  comm_d := id_comm_d M
  comm_smul := id_comm_smul M

/-- A composite of left-DG-module morphisms commutes with the differential. -/
theorem comp_comm_d {L M N : LeftDifferentialGradedModule A}
    (g : Hom M N) (f : Hom L M) (n : ℤ) (x : L.X n) :
    (g.hom (n + 1)).comp (f.hom (n + 1)) (L.d n x) =
      N.d n ((g.hom n).comp (f.hom n) x) := sorry

/-- A composite of left-DG-module morphisms commutes with the left action. -/
theorem comp_comm_smul {L M N : LeftDifferentialGradedModule A}
    (g : Hom M N) (f : Hom L M) (i p : ℤ) (a : A.X i) (x : L.X p) :
    (g.hom (i + p)).comp (f.hom (i + p)) (L.smul i p a x) =
      N.smul i p a ((g.hom p).comp (f.hom p) x) := sorry

/-- Composition of left-DG-module morphisms. -/
def comp {L M N : LeftDifferentialGradedModule A} (g : Hom M N) (f : Hom L M) : Hom L N where
  hom n := (g.hom n).comp (f.hom n)
  comm_d := comp_comm_d g f
  comm_smul := comp_comm_smul g f

/-- The degreewise map of the identity morphism. -/
@[simp] theorem id_hom (M : LeftDifferentialGradedModule A) (n : ℤ) :
    (id M).hom n = LinearMap.id := sorry

/-- The identity morphism acts identically on homogeneous elements. -/
@[simp] theorem id_apply (M : LeftDifferentialGradedModule A) (n : ℤ) (x : M.X n) :
    (id M).hom n x = x := sorry

/-- The degreewise map of a composite morphism. -/
@[simp] theorem comp_hom {L M N : LeftDifferentialGradedModule A}
    (g : Hom M N) (f : Hom L M) (n : ℤ) :
    (comp g f).hom n = (g.hom n).comp (f.hom n) := sorry

/-- A composite morphism acts degreewise by function composition. -/
@[simp] theorem comp_apply {L M N : LeftDifferentialGradedModule A}
    (g : Hom M N) (f : Hom L M) (n : ℤ) (x : L.X n) :
    (comp g f).hom n x = g.hom n (f.hom n x) := sorry

end Hom

/-- Left-DG-module morphisms are determined by their homogeneous components. -/
@[ext] theorem hom_ext {M N : LeftDifferentialGradedModule A} {f g : Hom M N}
    (h : ∀ n : ℤ, ∀ x : M.X n, f.hom n x = g.hom n x) : f = g := sorry

/-- A left-DG-module morphism acts degreewise on homogeneous elements. -/
instance instCoeFunHom {M : LeftDifferentialGradedModule.{u, v} A}
    {N : LeftDifferentialGradedModule.{u, w} A} :
    CoeFun (Hom M N) (fun _ ↦ ∀ n : ℤ, M.X n → N.X n) where
  coe f := fun n x ↦ f.hom n x

/-- Coercion to a function is the degreewise linear component. -/
@[simp] theorem coe_apply {M N : LeftDifferentialGradedModule A}
    (f : Hom M N) (n : ℤ) (x : M.X n) : f n x = f.hom n x := sorry

/-- A left-DG-module morphism commutes with the differential. -/
@[simp] theorem map_d_apply {M N : LeftDifferentialGradedModule A}
    (f : Hom M N) (n : ℤ) (x : M.X n) :
    f (n + 1) (M.d n x) = N.d n (f n x) := sorry

/-- A left-DG-module morphism is compatible with the left action. -/
@[simp] theorem map_smul_apply {M N : LeftDifferentialGradedModule A}
    (f : Hom M N) (i p : ℤ) (a : A.X i) (x : M.X p) :
    f (i + p) (M.smul i p a x) = N.smul i p a (f p x) := sorry

/-- The left identity category law for left-DG-module morphisms. -/
theorem id_comp {M N : LeftDifferentialGradedModule A} (f : Hom M N) :
    Hom.comp (Hom.id N) f = f := sorry

/-- The right identity category law for left-DG-module morphisms. -/
theorem comp_id {M N : LeftDifferentialGradedModule A} (f : Hom M N) :
    Hom.comp f (Hom.id M) = f := sorry

/-- Associativity of composition for left-DG-module morphisms. -/
theorem assoc {K L M N : LeftDifferentialGradedModule A}
    (h : Hom M N) (g : Hom L M) (f : Hom K L) :
    Hom.comp h (Hom.comp g f) = Hom.comp (Hom.comp h g) f := sorry

/-- Left differential graded modules over `A` form a category. -/
instance instCategory (A : CochainDGAlgebra R) : Category (LeftDifferentialGradedModule.{u, v} A) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp f g := Hom.comp g f
  id_comp := id_comp
  comp_id := comp_id
  assoc f g h := assoc h g f

end LeftDifferentialGradedModule
