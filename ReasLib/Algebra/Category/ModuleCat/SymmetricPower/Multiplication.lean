/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
    mulMultilinear M n m x y = ModuleCat.symmetricPower.mk (append x y) := by
  rfl

private theorem tprod_sumCongr
    {ι₁ ι₂ : Type*} {κ : Type u} (M : ModuleCat.{v} R)
    (s : ι₁ ⊕ ι₂ ≃ κ) (x : ι₁ → M) (y : ι₂ → M)
    (e : Equiv.Perm ι₁) (f : Equiv.Perm ι₂) :
    SymmetricPower.tprod R (Sum.elim (x ∘ e) (y ∘ f) ∘ s.symm) =
      SymmetricPower.tprod R (Sum.elim x y ∘ s.symm) := by
  let p := s.symm.trans ((Equiv.sumCongr e f).trans s)
  have h : Sum.elim (x ∘ e) (y ∘ f) ∘ s.symm = (Sum.elim x y ∘ s.symm) ∘ p := by
    funext i
    obtain ⟨j, rfl⟩ := s.surjective i
    cases j <;> simp [p]
  rw [h]
  exact SymmetricPower.tprod_equiv p _

/-- For a fixed left family, concatenation is invariant under permutations of the right family. -/
theorem mulMultilinear_isInvariant_right
    (M : ModuleCat.{v} R) (n m : ℕ) (x : SymmetricPower.UFin n → M) :
    SymmetricPower.IsInvariant (mulMultilinear M n m x) := by
  intro e y
  exact tprod_sumCongr M (sumUFinEquiv n m) x y (Equiv.refl _) e

/-- Multiplication by a pure left symmetric tensor, descended in the right argument. -/
noncomputable def mulRight
    (M : ModuleCat.{v} R) (n m : ℕ) (x : SymmetricPower.UFin n → M) :
    M.symmetricPower m →ₗ[R] M.symmetricPower (n + m) :=
  SymmetricPower.lift (mulMultilinear M n m x)
    (mulMultilinear_isInvariant_right M n m x)

private theorem mulRight_mk
    (M : ModuleCat.{v} R) (n m : ℕ)
    (x : SymmetricPower.UFin n → M) (y : SymmetricPower.UFin m → M) :
    mulRight M n m x (mk y) = mulMultilinear M n m x y := by
  exact SymmetricPower.lift_tprod _ _ y

/-- Updating a left input by a sum makes `mulRight` additive in that input. -/
theorem mulRight_update_add
    (M : ModuleCat.{v} R) (n m : ℕ) (x : SymmetricPower.UFin n → M)
    (i : SymmetricPower.UFin n) (a b : M) :
    mulRight M n m (Function.update x i (a + b)) =
      mulRight M n m (Function.update x i a) +
        mulRight M n m (Function.update x i b) := by
  apply SymmetricPower.linearMap_ext
  intro y
  change mulRight M n m (Function.update x i (a + b)) (mk y) =
    mulRight M n m (Function.update x i a) (mk y) +
      mulRight M n m (Function.update x i b) (mk y)
  simp only [mulRight_mk]
  exact congrArg (fun f ↦ f y) ((mulMultilinear M n m).map_update_add x i a b)

/-- Updating a left input by a scalar multiple makes `mulRight` linear in that input. -/
theorem mulRight_update_smul
    (M : ModuleCat.{v} R) (n m : ℕ) (x : SymmetricPower.UFin n → M)
    (i : SymmetricPower.UFin n) (r : R) (a : M) :
    mulRight M n m (Function.update x i (r • a)) =
      r • mulRight M n m (Function.update x i a) := by
  apply SymmetricPower.linearMap_ext
  intro y
  change mulRight M n m (Function.update x i (r • a)) (mk y) =
    r • mulRight M n m (Function.update x i a) (mk y)
  simp only [mulRight_mk]
  exact congrArg (fun f ↦ f y) ((mulMultilinear M n m).map_update_smul x i r a)

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
    SymmetricPower.IsInvariant (mulLeftMultilinear M n m) := by
  intro e x
  apply SymmetricPower.linearMap_ext
  intro y
  change mulRight M n m (x ∘ e) (mk y) = mulRight M n m x (mk y)
  rw [mulRight_mk, mulRight_mk, mulMultilinear_apply, mulMultilinear_apply]
  exact tprod_sumCongr M (sumUFinEquiv n m) x y e (Equiv.refl _)

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
    gradedMulFun M (x + x') y = gradedMulFun M x y + gradedMulFun M x' y := by
  simp [gradedMulFun]

/-- Symmetric-power multiplication is linear in its left argument. -/
theorem gradedMulFun_smul_left
    (M : ModuleCat.{v} R) {n m : ℕ}
    (r : R) (x : M.symmetricPower n) (y : M.symmetricPower m) :
    gradedMulFun M (r • x) y = r • gradedMulFun M x y := by
  simp [gradedMulFun]

/-- Symmetric-power multiplication is additive in its right argument. -/
theorem gradedMulFun_add_right
    (M : ModuleCat.{v} R) {n m : ℕ}
    (x : M.symmetricPower n) (y y' : M.symmetricPower m) :
    gradedMulFun M x (y + y') = gradedMulFun M x y + gradedMulFun M x y' := by
  simp [gradedMulFun]

/-- Symmetric-power multiplication is linear in its right argument. -/
theorem gradedMulFun_smul_right
    (M : ModuleCat.{v} R) {n m : ℕ}
    (r : R) (x : M.symmetricPower n) (y : M.symmetricPower m) :
    gradedMulFun M x (r • y) = r • gradedMulFun M x y := by
  simp [gradedMulFun]

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
    mul M n m (x ⊗ₜ[R] y) = gradedMulFun M x y := by
  rfl

/-- Symmetric-power multiplication concatenates pure symmetric tensors. -/
@[simp]
theorem mul_tmul_mk
    (M : ModuleCat.{v} R) (n m : ℕ)
    (x : SymmetricPower.UFin n → M) (y : SymmetricPower.UFin m → M) :
    mul M n m
        (ModuleCat.symmetricPower.mk x ⊗ₜ[R] ModuleCat.symmetricPower.mk y) =
      ModuleCat.symmetricPower.mk (append x y) := by
  have h : gradedMulLinear M n m (mk x) = mulRight M n m x :=
    SymmetricPower.lift_tprod _ _ x
  change gradedMulLinear M n m (mk x) (mk y) = _
  rw [h, mulRight_mk, mulMultilinear_apply]

/-- Symmetric-power multiplication is natural in the module. -/
theorem mul_naturality
    {M N : ModuleCat.{v} R} (f : M ⟶ N) (n m : ℕ) :
    ModuleCat.ofHom (TensorProduct.map (map f n).hom (map f m).hom) ≫ mul N n m =
      mul M n m ≫ map f (n + m) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply SymmetricPower.linearMap_ext
  intro x
  apply SymmetricPower.linearMap_ext
  intro y
  change mul N n m (map f n (mk x) ⊗ₜ[R] map f m (mk y)) =
    map f (n + m) (mul M n m (mk x ⊗ₜ[R] mk y))
  rw [map_mk, map_mk]
  calc
    mul N n m (mk (f ∘ x) ⊗ₜ[R] mk (f ∘ y)) =
        mk (append (f ∘ x) (f ∘ y)) := mul_tmul_mk N n m _ _
    _ = mk (f ∘ append x y) := by
      congr 1
      funext i
      dsimp only [append, Function.comp_apply]
      cases (sumUFinEquiv n m).symm i <;> rfl
    _ = map f (n + m) (mk (append x y)) := (map_mk f _).symm
    _ = map f (n + m) (mul M n m (mk x ⊗ₜ[R] mk y)) :=
      congrArg (map f (n + m)) (mul_tmul_mk M n m x y).symm

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
        (fun i : SymmetricPower.UFin 0 ↦ Fin.elim0 i.down) := by
  simp [oneLinear]

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
        (fun i : SymmetricPower.UFin 0 ↦ Fin.elim0 i.down) := by
  exact oneLinear_apply_one M

/-- The degree-zero unit is natural in the module. -/
theorem one_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    one M ≫ map f 0 = one N := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change map f 0 (one M 1) = one N 1
  rw [one_apply_one, map_mk, one_apply_one]
  congr 1
  exact funext fun i ↦ Fin.elim0 i.down

private theorem gradedMulFun_mk
    (M : ModuleCat.{v} R) (n m : ℕ)
    (x : SymmetricPower.UFin n → M) (y : SymmetricPower.UFin m → M) :
    gradedMulFun M (mk x) (mk y) = mk (append x y) := by
  exact mul_tmul_mk M n m x y

private theorem mk_eqToHom
    (M : ModuleCat.{v} R) {n m : ℕ} (h : n = m)
    (e : SymmetricPower.UFin n ≃ SymmetricPower.UFin m)
    (x : SymmetricPower.UFin n → M) (y : SymmetricPower.UFin m → M)
    (hxy : ∀ i, y (e i) = x i) :
    (eqToHom (congrArg (fun d ↦ M.symmetricPower d) h)) (mk x) = mk y := by
  subst m
  change SymmetricPower.tprod R x = SymmetricPower.tprod R y
  calc
    SymmetricPower.tprod R x = SymmetricPower.tprod R (y ∘ e) :=
      congrArg (SymmetricPower.tprod R) (funext hxy).symm
    _ = SymmetricPower.tprod R y := SymmetricPower.tprod_equiv e y

private theorem eqToHom_heq
    (M : ModuleCat.{v} R) {n m : ℕ} (h : n = m) (x : M.symmetricPower n) :
    HEq ((eqToHom (congrArg (fun d ↦ M.symmetricPower d) h)) x) x := by
  subst m
  rfl

/-- Fixed-degree symmetric multiplication is associative. -/
theorem gradedMulFun_assoc
    (M : ModuleCat.{v} R) {n m k : ℕ}
    (x : M.symmetricPower n) (y : M.symmetricPower m)
    (z : M.symmetricPower k) :
    HEq (gradedMulFun M (gradedMulFun M x y) z)
      (gradedMulFun M x (gradedMulFun M y z)) := by
  let t : M.symmetricPower ((n + m) + k) ⟶ M.symmetricPower (n + (m + k)) :=
    eqToHom (congrArg (fun d ↦ M.symmetricPower d) (Nat.add_assoc n m k))
  have h : t.hom.comp (((gradedMulLinear M (n + m) k).flip z).comp
      ((gradedMulLinear M n m).flip y)) =
      (gradedMulLinear M n (m + k)).flip (gradedMulFun M y z) := by
    apply SymmetricPower.linearMap_ext
    intro a
    suffices h : t.hom.comp (((gradedMulLinear M (n + m) k).flip z).comp
        (gradedMulLinear M n m (mk a))) =
        (gradedMulLinear M n (m + k) (mk a)).comp
          ((gradedMulLinear M m k).flip z) by
      exact DFunLike.congr_fun h y
    apply SymmetricPower.linearMap_ext
    intro b
    suffices h : t.hom.comp
        (gradedMulLinear M (n + m) k (gradedMulFun M (mk a) (mk b))) =
        (gradedMulLinear M n (m + k) (mk a)).comp (gradedMulLinear M m k (mk b)) by
      exact DFunLike.congr_fun h z
    apply SymmetricPower.linearMap_ext
    intro c
    change t (gradedMulFun M (gradedMulFun M (mk a) (mk b)) (mk c)) =
      gradedMulFun M (mk a) (gradedMulFun M (mk b) (mk c))
    simp only [gradedMulFun_mk]
    let l : ((SymmetricPower.UFin.{u} n ⊕ SymmetricPower.UFin.{u} m) ⊕
        SymmetricPower.UFin.{u} k) ≃ SymmetricPower.UFin.{u} ((n + m) + k) :=
      (Equiv.sumCongr (sumUFinEquiv.{u, u, u} n m) (Equiv.refl _)).trans (sumUFinEquiv.{u, u, u} (n + m) k)
    let r : ((SymmetricPower.UFin.{u} n ⊕ SymmetricPower.UFin.{u} m) ⊕
        SymmetricPower.UFin.{u} k) ≃ SymmetricPower.UFin.{u} (n + (m + k)) :=
      (Equiv.sumAssoc _ _ _).trans
        ((Equiv.sumCongr (Equiv.refl _) (sumUFinEquiv.{u, u, u} m k)).trans (sumUFinEquiv.{u, u, u} n (m + k)))
    apply mk_eqToHom M (Nat.add_assoc n m k) (l.symm.trans r)
    intro i
    obtain ⟨j, rfl⟩ := l.surjective i
    rcases j with (j | j) | j <;> simp [l, r, append]
  have hx := DFunLike.congr_fun h x
  exact (eqToHom_heq M (Nat.add_assoc n m k) _).symm.trans (heq_of_eq hx)

/-- Fixed-degree symmetric multiplication is commutative. -/
theorem gradedMulFun_comm
    (M : ModuleCat.{v} R) {n m : ℕ}
    (x : M.symmetricPower n) (y : M.symmetricPower m) :
    HEq (gradedMulFun M x y) (gradedMulFun M y x) := by
  let t : M.symmetricPower (n + m) ⟶ M.symmetricPower (m + n) :=
    eqToHom (congrArg (fun d ↦ M.symmetricPower d) (Nat.add_comm n m))
  have h : t.hom.comp ((gradedMulLinear M n m).flip y) = gradedMulLinear M m n y := by
    apply SymmetricPower.linearMap_ext
    intro a
    suffices h : t.hom.comp (gradedMulLinear M n m (mk a)) =
        (gradedMulLinear M m n).flip (mk a) by
      exact DFunLike.congr_fun h y
    apply SymmetricPower.linearMap_ext
    intro b
    change t (gradedMulFun M (mk a) (mk b)) = gradedMulFun M (mk b) (mk a)
    simp only [gradedMulFun_mk]
    let s : SymmetricPower.UFin.{u} n ⊕ SymmetricPower.UFin.{u} m ≃
        SymmetricPower.UFin.{u} (n + m) := sumUFinEquiv.{u, u, u} n m
    let e := s.symm.trans ((Equiv.sumComm _ _).trans (sumUFinEquiv.{u, u, u} m n))
    apply mk_eqToHom M (Nat.add_comm n m) e
    intro i
    obtain ⟨j, rfl⟩ := s.surjective i
    cases j <;> simp [e, s, append]
  have hx := DFunLike.congr_fun h x
  exact (eqToHom_heq M (Nat.add_comm n m) _).symm.trans (heq_of_eq hx)

/-- Symmetric-power multiplication is associative, with degree reindexing explicit. -/
theorem mul_assoc (M : ModuleCat.{u} R) (n m k : ℕ) :
    (α_ (M.symmetricPower n) (M.symmetricPower m) (M.symmetricPower k)).hom ≫
        (M.symmetricPower n ◁ mul M m k) ≫ mul M n (m + k) =
      (mul M n m ▷ M.symmetricPower k) ≫ mul M (n + m) k ≫
        eqToHom (congrArg (fun d ↦ M.symmetricPower d) (Nat.add_assoc n m k)) := by
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro x y z
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.associator_hom_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply]
  apply Eq.symm
  apply eq_of_heq
  exact (eqToHom_heq M (Nat.add_assoc n m k) _).trans
    (gradedMulFun_assoc M x y z)

/-- The degree-zero symmetric tensor is a left unit. -/
theorem one_mul (M : ModuleCat.{u} R) (n : ℕ) :
    (λ_ (M.symmetricPower n)).hom =
      (one M ▷ M.symmetricPower n) ≫ mul M 0 n ≫
        eqToHom (congrArg (fun d ↦ M.symmetricPower d) (Nat.zero_add n)) := by
  let t : M.symmetricPower (0 + n) ⟶ M.symmetricPower n :=
    eqToHom (congrArg (fun d ↦ M.symmetricPower d) (Nat.zero_add n))
  have h : t.hom.comp (gradedMulLinear M 0 n (one M 1)) = LinearMap.id := by
    apply SymmetricPower.linearMap_ext
    intro x
    change t (gradedMulFun M (one M 1) (mk x)) = mk x
    rw [one_apply_one, gradedMulFun_mk]
    let s : SymmetricPower.UFin.{u} 0 ⊕ SymmetricPower.UFin.{u} n ≃
        SymmetricPower.UFin.{u} (0 + n) := sumUFinEquiv.{u, u, u} 0 n
    apply mk_eqToHom M (Nat.zero_add n) (s.symm.trans (Equiv.emptySum _ _))
    intro i
    obtain ⟨j, rfl⟩ := s.surjective i
    cases j with
    | inl j => exact Fin.elim0 j.down
    | inr j => simp [s, append]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro r x
  have hr : one M r = r • one M (1 : R) := by
    simpa using (one M).hom.map_smul r (1 : R)
  change r • x = t.hom (gradedMulFun M (one M r) x)
  rw [hr, gradedMulFun_smul_left, map_smul]
  exact congrArg (r • ·) (DFunLike.congr_fun h x).symm

/-- The degree-zero symmetric tensor is a right unit. -/
theorem mul_one (M : ModuleCat.{u} R) (n : ℕ) :
    (ρ_ (M.symmetricPower n)).hom =
      (M.symmetricPower n ◁ one M) ≫ mul M n 0 ≫
        eqToHom (congrArg (fun d ↦ M.symmetricPower d) (Nat.add_zero n)) := by
  let t : M.symmetricPower (n + 0) ⟶ M.symmetricPower n :=
    eqToHom (congrArg (fun d ↦ M.symmetricPower d) (Nat.add_zero n))
  have h : t.hom.comp ((gradedMulLinear M n 0).flip (one M 1)) = LinearMap.id := by
    apply SymmetricPower.linearMap_ext
    intro x
    change t (gradedMulFun M (mk x) (one M 1)) = mk x
    rw [one_apply_one, gradedMulFun_mk]
    let s : SymmetricPower.UFin.{u} n ⊕ SymmetricPower.UFin.{u} 0 ≃
        SymmetricPower.UFin.{u} (n + 0) := sumUFinEquiv.{u, u, u} n 0
    apply mk_eqToHom M (Nat.add_zero n) (s.symm.trans (Equiv.sumEmpty _ _))
    intro i
    obtain ⟨j, rfl⟩ := s.surjective i
    cases j with
    | inl j => simp [s, append]
    | inr j => exact Fin.elim0 j.down
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x r
  have hr : one M r = r • one M (1 : R) := by
    simpa using (one M).hom.map_smul r (1 : R)
  change r • x = t.hom (gradedMulFun M x (one M r))
  rw [hr, gradedMulFun_smul_right, map_smul]
  exact congrArg (r • ·) (DFunLike.congr_fun h x).symm

/-- Symmetric-power multiplication commutes with the symmetric braiding. -/
theorem mul_braiding (M : ModuleCat.{u} R) (n m : ℕ) :
    (β_ (M.symmetricPower n) (M.symmetricPower m)).hom ≫ mul M m n =
      mul M n m ≫
        eqToHom (congrArg (fun d ↦ M.symmetricPower d) (Nat.add_comm n m)) := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.braiding_hom_apply]
  apply Eq.symm
  apply eq_of_heq
  exact (eqToHom_heq M (Nat.add_comm n m) _).trans (gradedMulFun_comm M x y)

end ModuleCat.symmetricPower
