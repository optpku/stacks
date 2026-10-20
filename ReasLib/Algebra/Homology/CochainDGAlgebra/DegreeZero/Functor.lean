/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import ReasLib.Algebra.Homology.CochainDGAlgebra.DegreeZero
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial degree-zero cochain DGAs

The object `CochainDGAlgebra.ofAlgebra R A` is functorial in the ordinary `R`-algebra `A`.
This leaf owns the induced cochain-DGA homomorphisms and the resulting functor from `AlgCat R`.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory ComplexShape HomologicalComplex

namespace CochainDGAlgebra

variable (R : Type u) [CommRing R]

section Maps

variable {A B C : Type v}
variable [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [Ring C] [Algebra R C]

/-- The cochain map between degree-zero complexes induced by an algebra homomorphism. -/
noncomputable def degreeZeroMap (f : A →ₐ[R] B) :
    degreeZeroComplex R A ⟶ degreeZeroComplex R B :=
  (single (ModuleCat.{v} R) (up ℤ) 0).map (ModuleCat.ofHom f.toLinearMap)

/-- In degree zero, `degreeZeroMap` evaluates as the original algebra homomorphism. -/
@[simp]
theorem degreeZeroMap_apply (f : A →ₐ[R] B)
    (x : (degreeZeroComplex R A).X 0) :
    (degreeZeroIso R B).hom ((degreeZeroMap R f).f 0 x) =
      f ((degreeZeroIso R A).hom x) := sorry

/-- The degree-zero cochain map induced by an algebra homomorphism preserves the DGA unit. -/
theorem degreeZeroMap_one (f : A →ₐ[R] B) :
    (degreeZeroMap R f).f 0 (ofAlgebra R A).one = (ofAlgebra R B).one := sorry

/-- The degree-zero cochain map induced by an algebra homomorphism preserves homogeneous
multiplication. -/
theorem degreeZeroMap_mul (f : A →ₐ[R] B) (n m : ℤ)
    (x : (ofAlgebra R A).X n) (y : (ofAlgebra R A).X m) :
    (degreeZeroMap R f).f (n + m) ((ofAlgebra R A).mul n m x y) =
      (ofAlgebra R B).mul n m ((degreeZeroMap R f).f n x)
        ((degreeZeroMap R f).f m y) := sorry

/-- An algebra homomorphism regarded as a morphism between the associated degree-zero cochain
DGAs. -/
@[stacks 09SC "ordinary algebra morphisms as degree-zero cochain-DGA morphisms"]
noncomputable def ofAlgebraHom (f : A →ₐ[R] B) :
    ofAlgebra R A ⟶ ofAlgebra R B where
  map n := ((degreeZeroMap R f).f n).hom
  comm_d := sorry
  map_one := degreeZeroMap_one R f
  map_mul := degreeZeroMap_mul R f

/-- The underlying cochain map of `ofAlgebraHom` is `degreeZeroMap`. -/
@[simp]
theorem ofAlgebraHom_toCochainMap (f : A →ₐ[R] B) :
    (ofAlgebraHom R f).toCochainMap = degreeZeroMap R f := sorry

/-- Evaluation of `ofAlgebraHom` in degree zero is evaluation of the original algebra
homomorphism. -/
@[simp]
theorem ofAlgebraHom_apply (f : A →ₐ[R] B)
    (x : (ofAlgebra R A).X 0) :
    (degreeZeroIso R B).hom (ofAlgebraHom R f 0 x) =
      f ((degreeZeroIso R A).hom x) := sorry

/-- The identity algebra homomorphism induces the identity degree-zero cochain-DGA morphism. -/
@[simp]
theorem ofAlgebraHom_id :
    ofAlgebraHom R (AlgHom.id R A) = 𝟙 (ofAlgebra R A) := sorry

/-- Degree-zero cochain-DGA morphisms preserve composition of algebra homomorphisms. -/
@[simp]
theorem ofAlgebraHom_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    ofAlgebraHom R (g.comp f) = ofAlgebraHom R f ≫ ofAlgebraHom R g := sorry

end Maps

/-- Place an ordinary algebra functorially in cochain degree zero. -/
@[stacks 09SC "degree-zero functor from ordinary algebras to cochain DGAs"]
noncomputable def degreeZero :
    AlgCat.{v} R ⥤ CochainDGAlgebra.{u, v} R where
  obj A := ofAlgebra R A
  map f := ofAlgebraHom R f.hom
  map_id := sorry
  map_comp := sorry

/-- The degree-zero functor sends an algebra to its canonical degree-zero cochain DGA. -/
@[simp]
theorem degreeZero_obj (A : AlgCat.{v} R) :
    (degreeZero R).obj A = ofAlgebra R A := sorry

/-- The degree-zero functor sends an algebra morphism to `ofAlgebraHom`. -/
@[simp]
theorem degreeZero_map {A B : AlgCat.{v} R} (f : A ⟶ B) :
    (degreeZero R).map f = ofAlgebraHom R f.hom := sorry

end CochainDGAlgebra
