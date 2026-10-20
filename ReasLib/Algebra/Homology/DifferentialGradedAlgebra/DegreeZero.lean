/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.HomologyZero

/-!
# Ordinary algebras as chain differential graded algebras

An ordinary commutative algebra has a canonical chain-DGA model supported in degree zero.  The
underlying complex is Mathlib's single-term complex, and its algebra structure is transported
through the canonical identification in degree zero.  This file also identifies the canonical
zeroth homology algebra of that model with the original algebra.
-/

@[expose] public section

noncomputable section

open CategoryTheory ComplexShape HomologicalComplex

universe u v

namespace ChainDGAlgebra

variable (R : Type u) [CommRing R]
variable (S : Type v) [CommRing S] [Algebra R S]

/-- The single-term chain complex underlying an ordinary algebra placed in degree zero. -/
@[stacks 09PN "infrastructure: single-term chain complex of an ordinary algebra"]
noncomputable abbrev degreeZeroComplex : ChainComplex (ModuleCat.{v} R) ℤ :=
  (single (ModuleCat.{v} R) (down ℤ) 0).obj (ModuleCat.of R S)

/-- The canonical identification of degree zero in `degreeZeroComplex R S` with `S`. -/
@[stacks 09PN "infrastructure: degree-zero identification for an ordinary algebra"]
noncomputable def degreeZeroIso :
    (degreeZeroComplex R S).X 0 ≅ ModuleCat.of R S :=
  singleObjXSelf (down ℤ) 0 (ModuleCat.of R S)

namespace Implementation

/-- Multiplication transported to degree zero is additive in its right input. -/
theorem degreeZeroMulValue_add_right
    (x y z : (degreeZeroComplex R S).X 0) :
    (degreeZeroIso R S).inv
        ((degreeZeroIso R S).hom x * (degreeZeroIso R S).hom (y + z)) =
      (degreeZeroIso R S).inv
          ((degreeZeroIso R S).hom x * (degreeZeroIso R S).hom y) +
        (degreeZeroIso R S).inv
          ((degreeZeroIso R S).hom x * (degreeZeroIso R S).hom z) := sorry

/-- Multiplication transported to degree zero is linear in its right input. -/
theorem degreeZeroMulValue_smul_right
    (r : R) (x y : (degreeZeroComplex R S).X 0) :
    (degreeZeroIso R S).inv
        ((degreeZeroIso R S).hom x * (degreeZeroIso R S).hom (r • y)) =
      r • (degreeZeroIso R S).inv
        ((degreeZeroIso R S).hom x * (degreeZeroIso R S).hom y) := sorry

/-- Left multiplication after transporting the ordinary product to degree zero. -/
noncomputable def degreeZeroMulLeft (x : (degreeZeroComplex R S).X 0) :
    (degreeZeroComplex R S).X 0 →ₗ[R] (degreeZeroComplex R S).X 0 where
  toFun y := (degreeZeroIso R S).inv
    ((degreeZeroIso R S).hom x * (degreeZeroIso R S).hom y)
  map_add' := degreeZeroMulValue_add_right R S x
  map_smul' := fun r y ↦ degreeZeroMulValue_smul_right R S r x y

/-- Transported left multiplication is additive in the fixed factor. -/
theorem degreeZeroMulLeft_add
    (x y : (degreeZeroComplex R S).X 0) :
    degreeZeroMulLeft R S (x + y) =
      degreeZeroMulLeft R S x + degreeZeroMulLeft R S y := sorry

/-- Transported left multiplication is linear in the fixed factor. -/
theorem degreeZeroMulLeft_smul
    (r : R) (x : (degreeZeroComplex R S).X 0) :
    degreeZeroMulLeft R S (r • x) = r • degreeZeroMulLeft R S x := sorry

/-- The bilinear multiplication on the degree-zero component of the single-term complex. -/
noncomputable def degreeZeroMulZero :
    (degreeZeroComplex R S).X 0 →ₗ[R]
      (degreeZeroComplex R S).X 0 →ₗ[R] (degreeZeroComplex R S).X 0 where
  toFun := degreeZeroMulLeft R S
  map_add' := degreeZeroMulLeft_add R S
  map_smul' := degreeZeroMulLeft_smul R S

/-- Homogeneous multiplication for the chain DGA of an ordinary algebra. -/
noncomputable def degreeZeroMul : (i j : ℤ) →
    (degreeZeroComplex R S).X i →ₗ[R]
      (degreeZeroComplex R S).X j →ₗ[R] (degreeZeroComplex R S).X (i + j)
  | 0, 0 => degreeZeroMulZero R S
  | _, _ => 0

/-- The homogeneous multiplication on the degree-zero model is associative. -/
theorem degreeZeroMul_assoc (i j k : ℤ)
    (x : (degreeZeroComplex R S).X i)
    (y : (degreeZeroComplex R S).X j)
    (z : (degreeZeroComplex R S).X k) :
    cast (congrArg (fun n : ℤ ↦ ((degreeZeroComplex R S).X n : Type v))
      (add_assoc i j k))
        (degreeZeroMul R S (i + j) k (degreeZeroMul R S i j x y) z) =
      degreeZeroMul R S i (j + k) x (degreeZeroMul R S j k y z) := sorry

/-- The transported ordinary unit acts on the left in every homogeneous degree. -/
theorem degreeZeroMul_one_mul (n : ℤ) (x : (degreeZeroComplex R S).X n) :
    cast (congrArg (fun i : ℤ ↦ ((degreeZeroComplex R S).X i : Type v))
      (zero_add n))
        (degreeZeroMul R S 0 n ((degreeZeroIso R S).inv (1 : S)) x) = x := sorry

/-- The transported ordinary unit acts on the right in every homogeneous degree. -/
theorem degreeZeroMul_mul_one (n : ℤ) (x : (degreeZeroComplex R S).X n) :
    cast (congrArg (fun i : ℤ ↦ ((degreeZeroComplex R S).X i : Type v))
      (add_zero n))
        (degreeZeroMul R S n 0 x ((degreeZeroIso R S).inv (1 : S))) = x := sorry

/-- The zero differential on the degree-zero model satisfies the chain Leibniz rule. -/
theorem degreeZeroMul_leibniz (n m : ℤ)
    (x : (degreeZeroComplex R S).X n) (y : (degreeZeroComplex R S).X m) :
    (degreeZeroComplex R S).d (n + m) (n + m - 1)
        (degreeZeroMul R S n m x y) =
      cast (congrArg (fun i : ℤ ↦ ((degreeZeroComplex R S).X i : Type v))
        (ChainDGAlgebra.leftLeibnizIndex n m))
          (degreeZeroMul R S (n - 1) m
            ((degreeZeroComplex R S).d n (n - 1) x) y) +
        n.negOnePow •
          cast (congrArg (fun i : ℤ ↦ ((degreeZeroComplex R S).X i : Type v))
            (ChainDGAlgebra.rightLeibnizIndex n m))
              (degreeZeroMul R S n (m - 1) x
                ((degreeZeroComplex R S).d m (m - 1) y)) := sorry

end Implementation

/-- An ordinary commutative `R`-algebra, regarded as a chain DGA supported in degree zero. -/
@[stacks 09PN "infrastructure: ordinary algebra as a degree-zero chain DGA"]
noncomputable def ofAlgebra : ChainDGAlgebra.{u, v} R where
  toChainComplex := degreeZeroComplex R S
  mul := Implementation.degreeZeroMul R S
  one := (degreeZeroIso R S).inv (1 : S)
  mul_assoc := Implementation.degreeZeroMul_assoc R S
  one_mul := Implementation.degreeZeroMul_one_mul R S
  mul_one := Implementation.degreeZeroMul_mul_one R S
  leibniz := Implementation.degreeZeroMul_leibniz R S

namespace Implementation

/-- Homogeneous multiplication in the degree-zero model obeys graded commutativity. -/
theorem ofAlgebra_mul_comm {n m : ℤ}
    (x : (ofAlgebra R S).X n) (y : (ofAlgebra R S).X m) :
    (ofAlgebra R S).mul n m x y =
      cast (congrArg (fun i : ℤ ↦ ((ofAlgebra R S).X i : Type v)) (add_comm m n))
        (((n * m).negOnePow : R) • (ofAlgebra R S).mul m n y x) := sorry

/-- Every odd-degree homogeneous element of the degree-zero model has square zero. -/
theorem ofAlgebra_sq_eq_zero_of_odd {n : ℤ} (hn : Odd n)
    (x : (ofAlgebra R S).X n) :
    (ofAlgebra R S).mul n n x x = 0 := sorry

end Implementation

/-- The chain DGA concentrated in degree zero is canonically strictly commutative. -/
noncomputable instance ofAlgebraIsStrictlyCommutative :
    (ofAlgebra R S).IsStrictlyCommutative where
  mul_comm := Implementation.ofAlgebra_mul_comm R S
  sq_eq_zero_of_odd := Implementation.ofAlgebra_sq_eq_zero_of_odd R S

section Maps

variable {S T U : Type v} [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] [CommRing U] [Algebra R U]

/-- The chain map between degree-zero complexes induced by an algebra homomorphism. -/
noncomputable def degreeZeroMap (f : S →ₐ[R] T) :
    degreeZeroComplex R S ⟶ degreeZeroComplex R T :=
  (single (ModuleCat.{v} R) (down ℤ) 0).map (ModuleCat.ofHom f.toLinearMap)

/-- Evaluation of the degree-zero chain map is evaluation of the original algebra homomorphism. -/
@[simp] theorem degreeZeroMap_apply (f : S →ₐ[R] T)
    (x : (degreeZeroComplex R S).X 0) :
    (degreeZeroIso R T).hom ((degreeZeroMap R f).f 0 x) =
      f ((degreeZeroIso R S).hom x) := sorry

namespace Implementation

/-- The degree-zero chain map induced by an algebra homomorphism preserves the unit. -/
theorem degreeZeroMap_one (f : S →ₐ[R] T) :
    (degreeZeroMap R f).f 0 (ofAlgebra R S).one = (ofAlgebra R T).one := sorry

/-- The degree-zero chain map induced by an algebra homomorphism preserves homogeneous
multiplication. -/
theorem degreeZeroMap_mul (f : S →ₐ[R] T) (n m : ℤ)
    (x : (ofAlgebra R S).X n) (y : (ofAlgebra R S).X m) :
    (degreeZeroMap R f).f (n + m) ((ofAlgebra R S).mul n m x y) =
      (ofAlgebra R T).mul n m ((degreeZeroMap R f).f n x)
        ((degreeZeroMap R f).f m y) := sorry

end Implementation

/-- An algebra homomorphism regarded as a morphism between the associated degree-zero chain
DGAs. -/
@[stacks 09PN "infrastructure: ordinary algebra morphisms as degree-zero chain-DGA morphisms"]
noncomputable def ofAlgebraHom (f : S →ₐ[R] T) :
    ofAlgebra R S ⟶ ofAlgebra R T where
  toChainMap := degreeZeroMap R f
  map_one := Implementation.degreeZeroMap_one R f
  map_mul := Implementation.degreeZeroMap_mul R f

/-- The underlying chain map of `ofAlgebraHom` is the map of single-term complexes. -/
@[simp] theorem ofAlgebraHom_toChainMap (f : S →ₐ[R] T) :
    (ofAlgebraHom R f).toChainMap = degreeZeroMap R f := sorry

/-- Evaluation of `ofAlgebraHom` in degree zero is evaluation of the original algebra
homomorphism. -/
@[simp] theorem ofAlgebraHom_apply (f : S →ₐ[R] T)
    (x : (ofAlgebra R S).X 0) :
    (degreeZeroIso R T).hom (ofAlgebraHom R f 0 x) =
      f ((degreeZeroIso R S).hom x) := sorry

/-- The identity algebra homomorphism induces the identity degree-zero chain-DGA morphism. -/
@[simp] theorem ofAlgebraHom_id :
    ofAlgebraHom R (AlgHom.id R S) = Hom.id (ofAlgebra R S) := sorry

/-- Degree-zero chain-DGA morphisms preserve composition of algebra homomorphisms. -/
@[simp] theorem ofAlgebraHom_comp (g : T →ₐ[R] U) (f : S →ₐ[R] T) :
    ofAlgebraHom R (g.comp f) =
      Hom.comp (ofAlgebraHom R g) (ofAlgebraHom R f) := sorry

end Maps

namespace Strict

/-- An ordinary commutative algebra bundled as a strictly commutative chain DGA concentrated in
degree zero. -/
@[stacks 09PN "infrastructure: ordinary algebra as a strict degree-zero chain DGA"]
noncomputable def ofAlgebra : Strict.{u, v} R where
  toChainDGAlgebra := ChainDGAlgebra.ofAlgebra R S

/-- The underlying chain DGA of the strict degree-zero object is the canonical degree-zero
model. -/
@[simp] theorem ofAlgebra_toChainDGAlgebra :
    (ofAlgebra R S).toChainDGAlgebra = ChainDGAlgebra.ofAlgebra R S := sorry

namespace Implementation

/-- The degree-zero assignment on ordinary algebras preserves categorical identities. -/
theorem degreeZero_map_id (A : CommAlgCat.{v} R) :
    (ChainDGAlgebra.ofAlgebraHom R (𝟙 A : A ⟶ A).hom :
      ofAlgebra R A ⟶ ofAlgebra R A) = 𝟙 (ofAlgebra R A) := sorry

/-- The degree-zero assignment on ordinary algebras preserves categorical composition. -/
theorem degreeZero_map_comp {A B C : CommAlgCat.{v} R}
    (f : A ⟶ B) (g : B ⟶ C) :
    (ChainDGAlgebra.ofAlgebraHom R (f ≫ g).hom :
      ofAlgebra R A ⟶ ofAlgebra R C) =
        (ChainDGAlgebra.ofAlgebraHom R f.hom :
          ofAlgebra R A ⟶ ofAlgebra R B) ≫
          (ChainDGAlgebra.ofAlgebraHom R g.hom :
            ofAlgebra R B ⟶ ofAlgebra R C) := sorry

end Implementation

/-- Place an ordinary commutative algebra functorially in chain degree zero. -/
@[stacks 09PN "infrastructure: degree-zero functor from ordinary algebras to strict chain DGAs"]
noncomputable def degreeZero (R : Type u) [CommRing R] :
    CommAlgCat.{v} R ⥤ ChainDGAlgebra.Strict.{u, v} R where
  obj A := ofAlgebra R A
  map f := ChainDGAlgebra.ofAlgebraHom R f.hom
  map_id A := Implementation.degreeZero_map_id R A
  map_comp f g := Implementation.degreeZero_map_comp R f g

/-- The degree-zero functor sends an algebra to its strict degree-zero chain-DGA model. -/
@[simp] theorem degreeZero_obj (A : CommAlgCat.{v} R) :
    (degreeZero R).obj A = ofAlgebra R A := sorry

/-- The degree-zero functor sends an algebra morphism to its canonical chain-DGA morphism. -/
@[simp] theorem degreeZero_map {A B : CommAlgCat.{v} R} (f : A ⟶ B) :
    (degreeZero R).map f =
      (ChainDGAlgebra.ofAlgebraHom R f.hom :
        ofAlgebra R A ⟶ ofAlgebra R B) := sorry

/-- Evaluation of the degree-zero functor is evaluation of the original algebra morphism. -/
@[simp] theorem degreeZero_map_apply {A B : CommAlgCat.{v} R}
    (f : A ⟶ B) (x : (ChainDGAlgebra.ofAlgebra R A).X 0) :
    (degreeZeroIso R B).hom ((degreeZero R).map f 0 x) =
      f ((degreeZeroIso R A).hom x) := sorry

end Strict

/-- The canonical module isomorphism from zeroth homology of the degree-zero model to `S`. -/
@[stacks 09PN "infrastructure: homology of a degree-zero chain DGA"]
noncomputable def homologyZeroIso :
    (ofAlgebra R S).toChainComplex.homology 0 ≅ ModuleCat.of R S :=
  singleObjHomologySelfIso (down ℤ) 0 (ModuleCat.of R S)

namespace Implementation

/-- The inverse of the single-term homology isomorphism is a left inverse. -/
theorem homologyZeroIso_left_inv (x : (ofAlgebra R S).homologyZero) :
    (homologyZeroIso R S).inv ((homologyZeroIso R S).hom x) = x := sorry

/-- The inverse of the single-term homology isomorphism is a right inverse. -/
theorem homologyZeroIso_right_inv (x : S) :
    (homologyZeroIso R S).hom ((homologyZeroIso R S).inv x) = x := sorry

/-- The single-term homology isomorphism preserves addition. -/
theorem homologyZeroIso_map_add (x y : (ofAlgebra R S).homologyZero) :
    (homologyZeroIso R S).hom (x + y) =
      (homologyZeroIso R S).hom x + (homologyZeroIso R S).hom y := sorry

/-- The single-term homology isomorphism preserves multiplication. -/
theorem homologyZeroIso_map_mul (x y : (ofAlgebra R S).homologyZero) :
    (homologyZeroIso R S).hom (x * y) =
      (homologyZeroIso R S).hom x * (homologyZeroIso R S).hom y := sorry

/-- The single-term homology isomorphism preserves the structural algebra map. -/
theorem homologyZeroIso_commutes (r : R) :
    (homologyZeroIso R S).hom
        (algebraMap R (ofAlgebra R S).homologyZero r) = algebraMap R S r := sorry

end Implementation

/-- Zeroth homology of an ordinary algebra placed in degree zero is canonically that algebra. -/
@[stacks 09PN "infrastructure: zeroth homology of a degree-zero chain DGA"]
noncomputable def homologyZeroEquiv : (ofAlgebra R S).homologyZero ≃ₐ[R] S where
  toFun := (homologyZeroIso R S).hom
  invFun := (homologyZeroIso R S).inv
  left_inv := Implementation.homologyZeroIso_left_inv R S
  right_inv := Implementation.homologyZeroIso_right_inv R S
  map_add' := Implementation.homologyZeroIso_map_add R S
  map_mul' := Implementation.homologyZeroIso_map_mul R S
  commutes' := Implementation.homologyZeroIso_commutes R S

/-- The canonical algebra equivalence is the forward single-term homology isomorphism. -/
@[simp] theorem homologyZeroEquiv_apply (x : (ofAlgebra R S).homologyZero) :
    homologyZeroEquiv R S x = (homologyZeroIso R S).hom x := sorry

/-- The inverse algebra equivalence is the inverse single-term homology isomorphism. -/
@[simp] theorem homologyZeroEquiv_symm_apply (x : S) :
    (homologyZeroEquiv R S).symm x = (homologyZeroIso R S).inv x := sorry

/-- On a cycle class, the canonical zeroth-homology equivalence is evaluation in degree zero. -/
@[simp] theorem homologyZeroEquiv_homologyπ (x : (ofAlgebra R S).cycles 0) :
    homologyZeroEquiv R S ((ofAlgebra R S).homologyπ 0 x) =
      (degreeZeroIso R S).hom ((ofAlgebra R S).iCycles 0 x) := sorry

end ChainDGAlgebra
