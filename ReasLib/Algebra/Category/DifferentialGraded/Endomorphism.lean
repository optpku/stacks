/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra

/-!
# Endomorphism DG Algebras

The graded homs of a differential graded category form cochain complexes.  Specializing both
objects to `x` gives the canonical endomorphism differential graded algebra of `x`.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace DifferentialGradedCategory

variable {R : Type u} [CommRing R]
variable {C : Type v} [D : DifferentialGradedCategory.{u, v, w} R C]

open scoped DifferentialGradedCategory

/-- The degree-`n` hom component from `x` to `y` in a differential graded category. -/
@[stacks 09LE "hom component in a differential graded category"]
abbrev homComponent (x y : C) (n : ℤ) : ModuleCat.{w} R :=
  ModuleCat.of R (x ⟶[n] y)

/-- The differential on the graded hom module, as a linear map. -/
@[stacks 09LE "differential on graded homs"]
def homDifferential (x y : C) (n : ℤ) :
    homComponent x y n →ₗ[R] homComponent x y (n + 1) where
  toFun := D.d n
  map_add' := sorry
  map_smul' := sorry

/-- The differential on graded homs squares to zero. -/
@[stacks 09LE "square-zero law for the graded hom differential"]
theorem homDifferential_sq (x y : C) (n : ℤ) :
    ModuleCat.ofHom (homDifferential x y n) ≫
      ModuleCat.ofHom (homDifferential x y (n + 1)) = 0 := sorry

/-- The cochain complex of graded morphisms from `x` to `y`. -/
@[stacks 09LE "graded hom cochain complex"]
def homComplex (x y : C) : CochainComplex (ModuleCat.{w} R) ℤ :=
  CochainComplex.of (homComponent x y) (fun n ↦ ModuleCat.ofHom (homDifferential x y n))
    (homDifferential_sq x y)

/-- The degree-`n` component of the graded hom complex is the corresponding homogeneous hom
module. -/
@[stacks 09LE "graded hom complex component", simp]
theorem homComplex_X (x y : C) (n : ℤ) :
    (homComplex x y).X n = homComponent x y n := sorry

/-- The differential of the graded hom complex is the differential of the DG category. -/
@[stacks 09LE "graded hom complex differential", simp]
theorem homComplex_d (x y : C) (n : ℤ) :
    ((homComplex x y).d n (n + 1)).hom = homDifferential x y n := sorry

/-- The value of homogeneous multiplication in the endomorphism DGA. -/
@[stacks 09LE "homogeneous endomorphism multiplication"]
def endomorphismMulValue (x : C) (n m : ℤ)
    (a : homComponent x x n) (b : homComponent x x m) : homComponent x x (n + m) :=
  @castHom ℤ (fun k : ℤ ↦ x ⟶[k] x) (m + n) (n + m)
    (Int.add_comm m n) (D.comp a b)

/-- Homogeneous composition as a bilinear multiplication on the endomorphism complex. -/
@[stacks 09LE "endomorphism DGA multiplication"]
def endomorphismMul (x : C) (n m : ℤ) :
    homComponent x x n →ₗ[R] homComponent x x m →ₗ[R] homComponent x x (n + m) where
  toFun := fun a ↦
    { toFun := endomorphismMulValue x n m a
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- The endomorphism differential graded algebra of an object in a differential graded category.
-/
@[stacks 09LE]
def endomorphismDGA (x : C) : CochainDGAlgebra.{u, w} R where
  toCochainComplex := homComplex x x
  mul := endomorphismMul x
  one := D.id x
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  leibniz := sorry

/-- The degree-`n` piece of `endomorphismDGA x` is the degree-`n` endomorphism module of `x`. -/
@[stacks 09LE "endomorphism DGA component", simp]
theorem endomorphismDGA_X (x : C) (n : ℤ) :
    (endomorphismDGA x).X n = homComponent x x n := sorry

/-- The differential of `endomorphismDGA x` is the differential on homogeneous endomorphisms.
-/
@[stacks 09LE "endomorphism DGA differential", simp]
theorem endomorphismDGA_d (x : C) (n : ℤ) :
    ((endomorphismDGA x).d n).hom = homDifferential x x n := sorry

/-- The unit of `endomorphismDGA x` is the identity homogeneous morphism. -/
@[stacks 09LE "endomorphism DGA unit", simp]
theorem endomorphismDGA_one (x : C) :
    (endomorphismDGA x).one = D.id x := sorry

/-- Multiplication in `endomorphismDGA x` is homogeneous composition. -/
@[stacks 09LE "endomorphism DGA multiplication evaluation", simp]
theorem endomorphismDGA_mul_apply (x : C) (n m : ℤ)
    (a : homComponent x x n) (b : homComponent x x m) :
    (endomorphismDGA x).mul n m a b = endomorphismMulValue x n m a b := sorry

end DifferentialGradedCategory
