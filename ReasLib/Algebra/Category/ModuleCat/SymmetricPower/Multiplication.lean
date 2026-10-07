module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.LinearAlgebra.Span.Basic
public import ReasLib.Algebra.Category.ModuleCat.SymmetricPower
public import ReasLib.LinearAlgebra.TensorPower.Symmetric.Lift
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication of symmetric powers in `ModuleCat`

The product concatenates the inputs of pure symmetric tensors.  It is constructed from the
universal quotient lift for permutation-invariant multilinear maps, rather than from a chosen
basis or from the full symmetric algebra.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u v w

namespace ModuleCat.symmetricPower

variable {R : Type u} [CommRing R]

/-- The canonical equivalence between the disjoint union of two universe-lifted finite index
types and the universe-lifted index type of their sum. -/
def sumUFinEquiv (n m : ℕ) :
    SymmetricPower.UFin n ⊕ SymmetricPower.UFin m ≃ SymmetricPower.UFin (n + m) :=
  (Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
    (finSumFinEquiv.trans Equiv.ulift.symm)

/-- Concatenation of two families indexed by universe-lifted finite types. -/
def append {M : Type w} {n m : ℕ}
    (x : SymmetricPower.UFin n → M) (y : SymmetricPower.UFin m → M) :
    SymmetricPower.UFin (n + m) → M :=
  Sum.elim x y ∘ (sumUFinEquiv n m).symm

/-- The curried multilinear map which concatenates two families and forms their pure symmetric
tensor. -/
noncomputable def mulMultilinear
    (M : ModuleCat.{v} R) (n m : ℕ) :
    MultilinearMap R (fun _ : SymmetricPower.UFin n ↦ M)
      (MultilinearMap R (fun _ : SymmetricPower.UFin m ↦ M)
        (M.symmetricPower (n + m))) :=
  MultilinearMap.currySum <|
    (SymmetricPower.tprod R
      (ι := SymmetricPower.UFin (n + m)) (M := M)).domDomCongr
        (sumUFinEquiv n m).symm

/-- The concatenation multilinear map evaluates to the pure symmetric tensor of the concatenated
family. -/
@[simp]
theorem mulMultilinear_apply
    (M : ModuleCat.{v} R) (n m : ℕ)
    (x : SymmetricPower.UFin n → M) (y : SymmetricPower.UFin m → M) :
    mulMultilinear M n m x y = ModuleCat.symmetricPower.mk (append x y) := sorry

/-- For a fixed left family, concatenation is invariant under permutations of the right family. -/
theorem mulMultilinear_isInvariant_right
    (M : ModuleCat.{v} R) (n m : ℕ) (x : SymmetricPower.UFin n → M) :
    SymmetricPower.IsInvariant (mulMultilinear M n m x) := sorry

/-- Multiplication by a pure left symmetric tensor, descended in the right argument. -/
noncomputable def mulRight
    (M : ModuleCat.{v} R) (n m : ℕ) (x : SymmetricPower.UFin n → M) :
    M.symmetricPower m →ₗ[R] M.symmetricPower (n + m) :=
  SymmetricPower.lift (mulMultilinear M n m x)
    (mulMultilinear_isInvariant_right M n m x)

/-- Updating a left input by a sum makes `mulRight` additive in that input. -/
theorem mulRight_update_add
    (M : ModuleCat.{v} R) (n m : ℕ) (x : SymmetricPower.UFin n → M)
    (i : SymmetricPower.UFin n) (a b : M) :
    mulRight M n m (Function.update x i (a + b)) =
      mulRight M n m (Function.update x i a) +
        mulRight M n m (Function.update x i b) := sorry

/-- Updating a left input by a scalar multiple makes `mulRight` linear in that input. -/
theorem mulRight_update_smul
    (M : ModuleCat.{v} R) (n m : ℕ) (x : SymmetricPower.UFin n → M)
    (i : SymmetricPower.UFin n) (r : R) (a : M) :
    mulRight M n m (Function.update x i (r • a)) =
      r • mulRight M n m (Function.update x i a) := sorry

/-- The multilinear map in the left family obtained after descending the right family to its
symmetric power. -/
noncomputable def mulLeftMultilinear
    (M : ModuleCat.{v} R) (n m : ℕ) :
    MultilinearMap R (fun _ : SymmetricPower.UFin n ↦ M)
      (M.symmetricPower m →ₗ[R] M.symmetricPower (n + m)) :=
  MultilinearMap.mk' (mulRight M n m)
    (mulRight_update_add M n m) (mulRight_update_smul M n m)

/-- The left-family multilinear map is invariant under permutations of the left family. -/
theorem mulLeftMultilinear_isInvariant
    (M : ModuleCat.{v} R) (n m : ℕ) :
    SymmetricPower.IsInvariant (mulLeftMultilinear M n m) := sorry

/-- The curried bilinear multiplication between two fixed symmetric degrees. -/
noncomputable def gradedMulLinear
    (M : ModuleCat.{v} R) (n m : ℕ) :
    M.symmetricPower n →ₗ[R]
      M.symmetricPower m →ₗ[R] M.symmetricPower (n + m) :=
  SymmetricPower.lift (mulLeftMultilinear M n m)
    (mulLeftMultilinear_isInvariant M n m)

/-- The underlying function of multiplication between two fixed symmetric degrees. -/
noncomputable def gradedMulFun
    (M : ModuleCat.{v} R) {n m : ℕ}
    (x : M.symmetricPower n) (y : M.symmetricPower m) :
    M.symmetricPower (n + m) :=
  gradedMulLinear M n m x y

/-- Symmetric-power multiplication is additive in its left argument. -/
theorem gradedMulFun_add_left
    (M : ModuleCat.{v} R) {n m : ℕ}
    (x x' : M.symmetricPower n) (y : M.symmetricPower m) :
    gradedMulFun M (x + x') y = gradedMulFun M x y + gradedMulFun M x' y := sorry

/-- Symmetric-power multiplication is linear in its left argument. -/
theorem gradedMulFun_smul_left
    (M : ModuleCat.{v} R) {n m : ℕ}
    (r : R) (x : M.symmetricPower n) (y : M.symmetricPower m) :
    gradedMulFun M (r • x) y = r • gradedMulFun M x y := sorry

/-- Symmetric-power multiplication is additive in its right argument. -/
theorem gradedMulFun_add_right
    (M : ModuleCat.{v} R) {n m : ℕ}
    (x : M.symmetricPower n) (y y' : M.symmetricPower m) :
    gradedMulFun M x (y + y') = gradedMulFun M x y + gradedMulFun M x y' := sorry

/-- Symmetric-power multiplication is linear in its right argument. -/
theorem gradedMulFun_smul_right
    (M : ModuleCat.{v} R) {n m : ℕ}
    (r : R) (x : M.symmetricPower n) (y : M.symmetricPower m) :
    gradedMulFun M x (r • y) = r • gradedMulFun M x y := sorry

/-- The multiplication morphism
`M.symmetricPower n ⊗ M.symmetricPower m ⟶ M.symmetricPower (n + m)`. -/
@[stacks 01CF "symmetric-power multiplication"]
noncomputable def mul (M : ModuleCat.{v} R) (n m : ℕ) :
    ModuleCat.of R (M.symmetricPower n ⊗[R] M.symmetricPower m) ⟶
      M.symmetricPower (n + m) :=
  ModuleCat.ofHom (TensorProduct.lift (gradedMulLinear M n m))

/-- Symmetric-power multiplication evaluates on a pure tensor by fixed-degree multiplication. -/
@[simp]
theorem mul_tmul
    (M : ModuleCat.{v} R) (n m : ℕ)
    (x : M.symmetricPower n) (y : M.symmetricPower m) :
    mul M n m (x ⊗ₜ[R] y) = gradedMulFun M x y := sorry

/-- Symmetric-power multiplication concatenates pure symmetric tensors. -/
@[simp]
theorem mul_tmul_mk
    (M : ModuleCat.{v} R) (n m : ℕ)
    (x : SymmetricPower.UFin n → M) (y : SymmetricPower.UFin m → M) :
    mul M n m
        (ModuleCat.symmetricPower.mk x ⊗ₜ[R] ModuleCat.symmetricPower.mk y) =
      ModuleCat.symmetricPower.mk (append x y) := sorry

/-- Symmetric-power multiplication is natural in the module. -/
theorem mul_naturality
    {M N : ModuleCat.{v} R} (f : M ⟶ N) (n m : ℕ) :
    ModuleCat.ofHom (TensorProduct.map (map f n).hom (map f m).hom) ≫ mul N n m =
      mul M n m ≫ map f (n + m) := sorry

/-- The linear degree-zero unit of symmetric-power multiplication, available independently of
the universe restriction on Mathlib's monoidal structure for `ModuleCat`. -/
@[stacks 01CF "universe-general degree-zero symmetric unit"]
noncomputable def oneLinear (M : ModuleCat.{v} R) :
    R →ₗ[R] M.symmetricPower 0 :=
  LinearMap.toSpanSingleton R _ <|
    ModuleCat.symmetricPower.mk (R := R) (M := M)
      (fun i : SymmetricPower.UFin 0 ↦ Fin.elim0 i.down)

/-- The linear degree-zero unit sends one to the empty pure symmetric tensor. -/
@[simp]
theorem oneLinear_apply_one (M : ModuleCat.{v} R) :
    oneLinear M (1 : R) =
      ModuleCat.symmetricPower.mk (R := R) (M := M)
        (fun i : SymmetricPower.UFin 0 ↦ Fin.elim0 i.down) := sorry

/-- The degree-zero unit of symmetric-power multiplication in the same-universe monoidal
category supported by Mathlib. -/
@[stacks 01CF "degree-zero unit for symmetric multiplication"]
noncomputable def one (M : ModuleCat.{u} R) :
    𝟙_ (ModuleCat.{u} R) ⟶ M.symmetricPower 0 :=
  ModuleCat.ofHom (oneLinear M)

/-- The degree-zero unit sends one to the empty pure symmetric tensor. -/
@[simp]
theorem one_apply_one (M : ModuleCat.{u} R) :
    one M (1 : R) =
      ModuleCat.symmetricPower.mk (R := R) (M := M)
        (fun i : SymmetricPower.UFin 0 ↦ Fin.elim0 i.down) := sorry

/-- The degree-zero unit is natural in the module. -/
theorem one_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    one M ≫ map f 0 = one N := sorry

/-- Fixed-degree symmetric multiplication is associative. -/
theorem gradedMulFun_assoc
    (M : ModuleCat.{v} R) {n m k : ℕ}
    (x : M.symmetricPower n) (y : M.symmetricPower m)
    (z : M.symmetricPower k) :
    HEq (gradedMulFun M (gradedMulFun M x y) z)
      (gradedMulFun M x (gradedMulFun M y z)) := sorry

/-- Fixed-degree symmetric multiplication is commutative. -/
theorem gradedMulFun_comm
    (M : ModuleCat.{v} R) {n m : ℕ}
    (x : M.symmetricPower n) (y : M.symmetricPower m) :
    HEq (gradedMulFun M x y) (gradedMulFun M y x) := sorry

/-- Symmetric-power multiplication is associative, with degree reindexing explicit. -/
theorem mul_assoc (M : ModuleCat.{u} R) (n m k : ℕ) :
    (α_ (M.symmetricPower n) (M.symmetricPower m) (M.symmetricPower k)).hom ≫
        (M.symmetricPower n ◁ mul M m k) ≫ mul M n (m + k) =
      (mul M n m ▷ M.symmetricPower k) ≫ mul M (n + m) k ≫
        eqToHom (congrArg (fun d ↦ M.symmetricPower d) (Nat.add_assoc n m k)) := sorry

/-- The degree-zero symmetric tensor is a left unit. -/
theorem one_mul (M : ModuleCat.{u} R) (n : ℕ) :
    (λ_ (M.symmetricPower n)).hom =
      (one M ▷ M.symmetricPower n) ≫ mul M 0 n ≫
        eqToHom (congrArg (fun d ↦ M.symmetricPower d) (Nat.zero_add n)) := sorry

/-- The degree-zero symmetric tensor is a right unit. -/
theorem mul_one (M : ModuleCat.{u} R) (n : ℕ) :
    (ρ_ (M.symmetricPower n)).hom =
      (M.symmetricPower n ◁ one M) ≫ mul M n 0 ≫
        eqToHom (congrArg (fun d ↦ M.symmetricPower d) (Nat.add_zero n)) := sorry

/-- Symmetric-power multiplication commutes with the symmetric braiding. -/
theorem mul_braiding (M : ModuleCat.{u} R) (n m : ℕ) :
    (β_ (M.symmetricPower n) (M.symmetricPower m)).hom ≫ mul M m n =
      mul M n m ≫
        eqToHom (congrArg (fun d ↦ M.symmetricPower d) (Nat.add_comm n m)) := sorry

end ModuleCat.symmetricPower
