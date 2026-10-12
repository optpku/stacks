/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Differential Graded Algebras

This leaf owns the elementary chain and cochain differential graded algebra
structures over a commutative ring, together with the concrete homogeneous
component API used by differential graded modules.
-/

@[expose] public section

universe u v

open CategoryTheory

variable {R : Type u} [CommRing R]

namespace ChainDGAlgebra

/-- Reassociates the left term in the chain Leibniz rule. -/
theorem leftLeibnizIndex (n m : ℤ) :
    (n - 1) + m = n + m - 1 := sorry

/-- Reassociates the right term in the chain Leibniz rule. -/
theorem rightLeibnizIndex (n m : ℤ) :
    n + (m - 1) = n + m - 1 := sorry

end ChainDGAlgebra

/-- Definition 22.3.1 (1): a chain differential graded algebra over `R`, with homogeneous
multiplication and the chain Leibniz rule. -/
@[stacks 061V]
structure ChainDGAlgebra (R : Type u) [CommRing R] where
  /-- The underlying chain complex of `R`-modules. -/
  toChainComplex : ChainComplex (ModuleCat.{v} R) ℤ
  /-- The degreewise multiplication maps. -/
  mul (n m : ℤ) : toChainComplex.X n →ₗ[R] toChainComplex.X m →ₗ[R] toChainComplex.X (n + m)
  /-- The unit element in degree `0`. -/
  one : toChainComplex.X 0
  /-- Homogeneous multiplication is associative. -/
  mul_assoc (i j k : ℤ) (a : toChainComplex.X i) (b : toChainComplex.X j)
      (c : toChainComplex.X k) :
      cast (congrArg (fun n : ℤ ↦ (toChainComplex.X n : Type v)) (add_assoc i j k))
        (mul (i + j) k (mul i j a b) c) =
        mul i (j + k) a (mul j k b c)
  /-- The unit acts on the left. -/
  one_mul (n : ℤ) (a : toChainComplex.X n) :
      cast (congrArg (fun i : ℤ ↦ (toChainComplex.X i : Type v)) (zero_add n))
        (mul 0 n one a) = a
  /-- The unit acts on the right. -/
  mul_one (n : ℤ) (a : toChainComplex.X n) :
      cast (congrArg (fun i : ℤ ↦ (toChainComplex.X i : Type v)) (add_zero n))
        (mul n 0 a one) = a
  /-- The differential satisfies the chain Leibniz rule. -/
  leibniz (n m : ℤ) (a : toChainComplex.X n) (b : toChainComplex.X m) :
      toChainComplex.d (n + m) (n + m - 1) (mul n m a b) =
        cast (congrArg (fun i : ℤ ↦ (toChainComplex.X i : Type v))
          (ChainDGAlgebra.leftLeibnizIndex n m))
          (mul (n - 1) m (toChainComplex.d n (n - 1) a) b) +
        n.negOnePow •
          cast (congrArg (fun i : ℤ ↦ (toChainComplex.X i : Type v))
            (ChainDGAlgebra.rightLeibnizIndex n m))
            (mul n (m - 1) a (toChainComplex.d m (m - 1) b))

namespace ChainDGAlgebra

/-- A chain differential graded algebra coerces to its underlying chain complex. -/
instance : CoeOut (ChainDGAlgebra.{u, v} R)
    (ChainComplex (ModuleCat.{v} R) ℤ) where
  coe A := A.toChainComplex

/-- The degree-`n` term of a chain differential graded algebra. -/
abbrev X (A : ChainDGAlgebra.{u, v} R) (n : ℤ) : ModuleCat.{v} R :=
  A.toChainComplex.X n

/-- The differential on degree `n` of a chain differential graded algebra. -/
abbrev d (A : ChainDGAlgebra.{u, v} R) (n : ℤ) : A.X n ⟶ A.X (n - 1) :=
  A.toChainComplex.d n (n - 1)

/-- The cycles object in degree `n`. -/
noncomputable abbrev cycles (A : ChainDGAlgebra.{u, v} R) (n : ℤ) :=
  A.toChainComplex.cycles n

/-- The canonical inclusion of cycles in degree `n`. -/
noncomputable abbrev iCycles (A : ChainDGAlgebra.{u, v} R) (n : ℤ) :
    A.cycles n ⟶ A.X n :=
  A.toChainComplex.iCycles n

/-- The homology object in degree `n`. -/
noncomputable abbrev homology (A : ChainDGAlgebra.{u, v} R) (n : ℤ) :=
  A.toChainComplex.homology n

/-- The canonical map from cycles to homology in degree `n`. -/
noncomputable abbrev homologyπ (A : ChainDGAlgebra.{u, v} R) (n : ℤ) :
    A.cycles n ⟶ A.homology n :=
  A.toChainComplex.homologyπ n

/-- The homogeneous component accessor is the underlying chain-complex component. -/
@[simp] theorem X_eq_toChainComplex_X (A : ChainDGAlgebra.{u, v} R) (n : ℤ) :
    A.X n = A.toChainComplex.X n := sorry

/-- The differential accessor is the underlying chain-complex differential. -/
@[simp] theorem d_eq_toChainComplex_d (A : ChainDGAlgebra.{u, v} R) (n : ℤ) :
    A.d n = A.toChainComplex.d n (n - 1) := sorry

/-- Homogeneous multiplication is associative. -/
theorem mul_assoc_apply (A : ChainDGAlgebra.{u, v} R) (i j k : ℤ)
    (a : A.X i) (b : A.X j) (c : A.X k) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) (add_assoc i j k))
      (A.mul (i + j) k (A.mul i j a b) c) =
      A.mul i (j + k) a (A.mul j k b c) := sorry

/-- The homogeneous left unit law. -/
@[simp] theorem one_mul_apply (A : ChainDGAlgebra.{u, v} R) (n : ℤ) (a : A.X n) :
    cast (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (zero_add n))
      (A.mul 0 n A.one a) = a := sorry

/-- The homogeneous right unit law. -/
@[simp] theorem mul_one_apply (A : ChainDGAlgebra.{u, v} R) (n : ℤ) (a : A.X n) :
    cast (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (add_zero n))
      (A.mul n 0 a A.one) = a := sorry

/-- The chain Leibniz rule on homogeneous elements. -/
theorem leibniz_apply (A : ChainDGAlgebra.{u, v} R) (n m : ℤ)
    (a : A.X n) (b : A.X m) :
    A.d (n + m) (A.mul n m a b) =
      cast (congrArg (fun i : ℤ ↦ (A.X i : Type v))
          (ChainDGAlgebra.leftLeibnizIndex n m))
          (A.mul (n - 1) m (A.d n a) b) +
        n.negOnePow •
          cast (congrArg (fun i : ℤ ↦ (A.X i : Type v))
              (ChainDGAlgebra.rightLeibnizIndex n m))
            (A.mul n (m - 1) a (A.d m b)) := sorry

end ChainDGAlgebra

/-- Definition 22.3.2 (1): a homomorphism of chain differential graded algebras. -/
@[stacks 061X]
structure ChainDGAlgebra.Hom
    (A B : ChainDGAlgebra.{u, v} R) where
  /-- The underlying chain map. -/
  toChainMap : A.toChainComplex ⟶ B.toChainComplex
  /-- The unit is preserved. -/
  map_one : toChainMap.f 0 A.one = B.one
  /-- Homogeneous multiplication is preserved. -/
  map_mul (n m : ℤ) (a : A.X n) (b : A.X m) :
    toChainMap.f (n + m) (A.mul n m a b) = B.mul n m (toChainMap.f n a) (toChainMap.f m b)

namespace ChainDGAlgebra.Hom

variable {A B C : ChainDGAlgebra.{u, v} R}

/-- The identity chain-DGA homomorphism. -/
def id (A : ChainDGAlgebra.{u, v} R) : Hom A A where
  toChainMap := 𝟙 A.toChainComplex
  map_one := rfl
  map_mul _ _ _ _ := rfl

/-- Composition of chain-DGA homomorphisms. -/
def comp (g : Hom B C) (f : Hom A B) : Hom A C where
  toChainMap := f.toChainMap ≫ g.toChainMap
  map_one := sorry
  map_mul _ _ _ _ := sorry

/-- The underlying map of the identity chain-DGA homomorphism. -/
@[simp] theorem id_toChainMap (A : ChainDGAlgebra.{u, v} R) :
    (id A).toChainMap = 𝟙 A.toChainComplex := sorry

/-- The underlying map of a composite chain-DGA homomorphism. -/
@[simp] theorem comp_toChainMap (g : Hom B C) (f : Hom A B) :
    (comp g f).toChainMap = f.toChainMap ≫ g.toChainMap := sorry

/-- Chain-DGA homomorphisms are determined by their underlying chain maps. -/
theorem ext_toChainMap {f g : Hom A B} (h : f.toChainMap = g.toChainMap) : f = g := sorry

/-- A chain-DGA homomorphism is surjective in every degree. -/
def Surjective (f : Hom A B) : Prop :=
  ∀ n : ℤ, Function.Surjective (f.toChainMap.f n)

/-- A chain-DGA homomorphism is injective in every degree. -/
def Injective (f : Hom A B) : Prop :=
  ∀ n : ℤ, Function.Injective (f.toChainMap.f n)

/-- A chain-DGA homomorphism is bijective in every degree. -/
def Bijective (f : Hom A B) : Prop :=
  f.Injective ∧ f.Surjective

/-- The identity chain-DGA homomorphism is degreewise surjective. -/
theorem id_surjective (A : ChainDGAlgebra.{u, v} R) : (id A).Surjective := sorry

/-- The identity chain-DGA homomorphism is degreewise injective. -/
theorem id_injective (A : ChainDGAlgebra.{u, v} R) : (id A).Injective := sorry

/-- The identity chain-DGA homomorphism is degreewise bijective. -/
theorem id_bijective (A : ChainDGAlgebra.{u, v} R) : (id A).Bijective := sorry

/-- A composite of degreewise surjective chain-DGA homomorphisms is degreewise surjective. -/
theorem comp_surjective (g : Hom B C) (f : Hom A B)
    (hg : g.Surjective) (hf : f.Surjective) : (comp g f).Surjective := sorry

/-- A composite of degreewise injective chain-DGA homomorphisms is degreewise injective. -/
theorem comp_injective (g : Hom B C) (f : Hom A B)
    (hg : g.Injective) (hf : f.Injective) : (comp g f).Injective := sorry

/-- A composite of degreewise bijective chain-DGA homomorphisms is degreewise bijective. -/
theorem comp_bijective (g : Hom B C) (f : Hom A B)
    (hg : g.Bijective) (hf : f.Bijective) : (comp g f).Bijective := sorry

end ChainDGAlgebra.Hom

namespace ChainDGAlgebra

/-- A chain-DGA homomorphism coerces to its underlying chain map. -/
instance {A B : ChainDGAlgebra.{u, v} R} :
    Coe (Hom A B) (A.toChainComplex ⟶ B.toChainComplex) where
  coe f := f.toChainMap

/-- A chain-DGA homomorphism acts degreewise on homogeneous elements. -/
instance {A B : ChainDGAlgebra.{u, v} R} :
    CoeFun (Hom A B) (fun _ ↦ ∀ n : ℤ, A.X n → B.X n) where
  coe f := fun n a ↦ f.toChainMap.f n a

/-- Coercion to a function is the degreewise action of the underlying chain map. -/
@[simp] theorem coe_apply {A B : ChainDGAlgebra.{u, v} R}
    (f : Hom A B) (n : ℤ) (a : A.X n) :
    f n a = f.toChainMap.f n a := sorry

/-- A chain-DGA homomorphism commutes with differentials. -/
@[simp] theorem map_d_apply {A B : ChainDGAlgebra.{u, v} R}
    (f : Hom A B) (n : ℤ) (a : A.X n) :
    f (n - 1) (A.d n a) = B.d n (f n a) := sorry

/-- A chain-DGA homomorphism preserves the unit. -/
@[simp] theorem map_one_apply {A B : ChainDGAlgebra.{u, v} R} (f : Hom A B) :
    f 0 A.one = B.one := sorry

/-- A chain-DGA homomorphism preserves homogeneous multiplication. -/
@[simp] theorem map_mul_apply {A B : ChainDGAlgebra.{u, v} R} (f : Hom A B)
    (n m : ℤ) (a : A.X n) (b : A.X m) :
    f (n + m) (A.mul n m a b) = B.mul n m (f n a) (f m b) := sorry

/-- Chain-DGA homomorphism composition acts degreewise by function composition. -/
@[simp] theorem comp_apply {A B C : ChainDGAlgebra.{u, v} R}
    (g : Hom B C) (f : Hom A B)
    (n : ℤ) (a : A.X n) :
    Hom.comp g f n a = g n (f n a) := sorry

/-- Chain-DGA homomorphisms are determined degreewise. -/
@[ext] theorem hom_ext {A B : ChainDGAlgebra.{u, v} R} {f g : Hom A B}
    (h : ∀ n : ℤ, ∀ a : A.X n, f n a = g n a) : f = g := sorry

end ChainDGAlgebra

namespace CochainDGAlgebra

/-- Reassociates the left term in the cochain Leibniz rule. -/
theorem leftLeibnizIndex (n m : ℤ) :
    (n + 1) + m = n + m + 1 := sorry

/-- Reassociates the right term in the cochain Leibniz rule. -/
theorem rightLeibnizIndex (n m : ℤ) :
    n + (m + 1) = n + m + 1 := sorry

end CochainDGAlgebra

/-- Definition 22.3.1 (2): a cochain differential graded algebra over `R`, with homogeneous
multiplication and the cochain Leibniz rule. -/
@[stacks 061V]
structure CochainDGAlgebra (R : Type u) [CommRing R] where
  /-- The underlying cochain complex of `R`-modules. -/
  toCochainComplex : CochainComplex (ModuleCat.{v} R) ℤ
  /-- The degreewise multiplication maps. -/
  mul (n m : ℤ) :
      toCochainComplex.X n →ₗ[R] toCochainComplex.X m →ₗ[R] toCochainComplex.X (n + m)
  /-- The unit element in degree `0`. -/
  one : toCochainComplex.X 0
  /-- Homogeneous multiplication is associative. -/
  mul_assoc (i j k : ℤ) (a : toCochainComplex.X i) (b : toCochainComplex.X j)
      (c : toCochainComplex.X k) :
      cast (congrArg (fun n : ℤ ↦ (toCochainComplex.X n : Type v)) (add_assoc i j k))
        (mul (i + j) k (mul i j a b) c) =
        mul i (j + k) a (mul j k b c)
  /-- The unit acts on the left. -/
  one_mul (n : ℤ) (a : toCochainComplex.X n) :
      cast (congrArg (fun i : ℤ ↦ (toCochainComplex.X i : Type v)) (zero_add n))
        (mul 0 n one a) = a
  /-- The unit acts on the right. -/
  mul_one (n : ℤ) (a : toCochainComplex.X n) :
      cast (congrArg (fun i : ℤ ↦ (toCochainComplex.X i : Type v)) (add_zero n))
        (mul n 0 a one) = a
  /-- The differential satisfies the cochain Leibniz rule. -/
  leibniz (n m : ℤ) (a : toCochainComplex.X n) (b : toCochainComplex.X m) :
      toCochainComplex.d (n + m) (n + m + 1) (mul n m a b) =
        cast (congrArg (fun i : ℤ ↦ (toCochainComplex.X i : Type v))
          (CochainDGAlgebra.leftLeibnizIndex n m))
          (mul (n + 1) m (toCochainComplex.d n (n + 1) a) b) +
        n.negOnePow •
          cast (congrArg (fun i : ℤ ↦ (toCochainComplex.X i : Type v))
            (CochainDGAlgebra.rightLeibnizIndex n m))
            (mul n (m + 1) a (toCochainComplex.d m (m + 1) b))

namespace CochainDGAlgebra

/-- A cochain differential graded algebra coerces to its underlying cochain complex. -/
instance : CoeOut (CochainDGAlgebra.{u, v} R)
    (CochainComplex (ModuleCat.{v} R) ℤ) where
  coe A := A.toCochainComplex

/-- The degree-`n` term of a cochain differential graded algebra. -/
abbrev X (A : CochainDGAlgebra.{u, v} R) (n : ℤ) : ModuleCat.{v} R :=
  A.toCochainComplex.X n

/-- The differential on degree `n` of a cochain differential graded algebra. -/
abbrev d (A : CochainDGAlgebra.{u, v} R) (n : ℤ) : A.X n ⟶ A.X (n + 1) :=
  A.toCochainComplex.d n (n + 1)

/-- The cycles object in degree `n`. -/
noncomputable abbrev cycles (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :=
  A.toCochainComplex.cycles n

/-- The canonical inclusion of cycles in degree `n`. -/
noncomputable abbrev iCycles (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    A.cycles n ⟶ A.X n :=
  A.toCochainComplex.iCycles n

/-- The homology object in degree `n`. -/
noncomputable abbrev homology (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :=
  A.toCochainComplex.homology n

/-- The canonical map from cycles to homology in degree `n`. -/
noncomputable abbrev homologyπ (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    A.cycles n ⟶ A.homology n :=
  A.toCochainComplex.homologyπ n

/-- The homogeneous component accessor is the underlying cochain-complex component. -/
@[simp] theorem X_eq_toCochainComplex_X (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    A.X n = A.toCochainComplex.X n := sorry

/-- The differential accessor is the underlying cochain-complex differential. -/
@[simp] theorem d_eq_toCochainComplex_d (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    A.d n = A.toCochainComplex.d n (n + 1) := sorry

/-- Homogeneous multiplication is associative. -/
theorem mul_assoc_apply (A : CochainDGAlgebra.{u, v} R) (i j k : ℤ)
    (a : A.X i) (b : A.X j) (c : A.X k) :
    cast (congrArg (fun n : ℤ ↦ (A.X n : Type v)) (add_assoc i j k))
      (A.mul (i + j) k (A.mul i j a b) c) =
      A.mul i (j + k) a (A.mul j k b c) := sorry

/-- The homogeneous left unit law. -/
@[simp] theorem one_mul_apply (A : CochainDGAlgebra.{u, v} R) (n : ℤ) (a : A.X n) :
    cast (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (zero_add n))
      (A.mul 0 n A.one a) = a := sorry

/-- The homogeneous right unit law. -/
@[simp] theorem mul_one_apply (A : CochainDGAlgebra.{u, v} R) (n : ℤ) (a : A.X n) :
    cast (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (add_zero n))
      (A.mul n 0 a A.one) = a := sorry

/-- The cochain Leibniz rule on homogeneous elements. -/
theorem leibniz_apply (A : CochainDGAlgebra.{u, v} R) (n m : ℤ)
    (a : A.X n) (b : A.X m) :
    A.d (n + m) (A.mul n m a b) =
      cast (congrArg (fun i : ℤ ↦ (A.X i : Type v))
          (CochainDGAlgebra.leftLeibnizIndex n m))
          (A.mul (n + 1) m (A.d n a) b) +
        n.negOnePow •
          cast (congrArg (fun i : ℤ ↦ (A.X i : Type v))
              (CochainDGAlgebra.rightLeibnizIndex n m))
            (A.mul n (m + 1) a (A.d m b)) := sorry

end CochainDGAlgebra
