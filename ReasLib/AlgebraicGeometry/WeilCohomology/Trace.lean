/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Graded.External
public import Mathlib.LinearAlgebra.TensorProduct.Map

@[expose] public section

noncomputable section

universe u v w

open scoped TensorProduct DirectSum

namespace WeilCohomology


namespace Tate

/-- The external Tate line F(n), formed from tensor powers of L or its dual. -/
abbrev Power (F : Type u) [Field F] (L : Type v) [AddCommGroup L] [Module F L] :
    ℤ → Type (max u v)
  | .ofNat n => TensorPower F n L
  | .negSucc n => TensorPower F (n + 1) (Module.Dual F L)

instance powerAddCommGroup (F : Type u) [Field F] (L : Type v)
    [AddCommGroup L] [Module F L] : (n : ℤ) → AddCommGroup (Power F L n)
  | .ofNat n => inferInstanceAs (AddCommGroup (TensorPower F n L))
  | .negSucc n => inferInstanceAs (AddCommGroup (TensorPower F (n + 1) (Module.Dual F L)))

instance powerModule (F : Type u) [Field F] (L : Type v)
    [AddCommGroup L] [Module F L] : (n : ℤ) → Module F (Power F L n)
  | .ofNat n => inferInstanceAs (Module F (TensorPower F n L))
  | .negSucc n => inferInstanceAs (Module F (TensorPower F (n + 1) (Module.Dual F L)))

/-- A coordinate on a genuine one-dimensional line, using mathlib's proved basis
construction. No existence axiom for an equivalence is used here. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def lineCoordinate {F : Type u} [Field F] {L : Type v}
    [AddCommGroup L] [Module F L] (hL : Module.finrank F L = 1) : L ≃ₗ[F] F :=
  (Module.basisUnique Unit hL).equivFun ≪≫ₗ LinearEquiv.funUnique Unit F F

/-- Tensor-power coordinates induced by a specified coordinate on the line. -/
def tensorCoordinate {F : Type u} [Field F] {L : Type v}
    [AddCommGroup L] [Module F L] (e : L ≃ₗ[F] F) :
    (n : ℕ) → TensorPower F n L ≃ₗ[F] F
  | 0 => PiTensorProduct.isEmptyEquiv (Fin 0)
  | n + 1 => (TensorPower.mulEquiv (R := F) (M := L) (n := n) (m := 1)).symm ≪≫ₗ
      TensorProduct.congr (tensorCoordinate e n)
        ((PiTensorProduct.subsingletonEquiv (0 : Fin 1)) ≪≫ₗ e) ≪≫ₗ
      TensorProduct.lid F F

/-- Coordinates on positive and negative Tate powers. These are auxiliary
coordinates; the twisted objects themselves are external tensor products. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def coordinate {F : Type u} [Field F] {L : Type v}
    [AddCommGroup L] [Module F L] (hL : Module.finrank F L = 1) :
    (n : ℤ) → Power F L n ≃ₗ[F] F
  | .ofNat n => tensorCoordinate (lineCoordinate hL) n
  | .negSucc n => tensorCoordinate
      ((lineCoordinate hL).dualMap.symm ≪≫ₗ LinearMap.ringLmapEquivSelf F F F) (n + 1)

/-- An n-th twist of a vector space. It is not a summand of that vector space. -/
abbrev Twist (F : Type u) [Field F] (L : Type v) [AddCommGroup L] [Module F L]
    (M : Type w) [AddCommGroup M] [Module F M] (n : ℤ) := M ⊗[F] Power F L n

def trivialization {F : Type u} [Field F] {L : Type v}
    [AddCommGroup L] [Module F L] (hL : Module.finrank F L = 1)
    (M : Type w) [AddCommGroup M] [Module F M] (n : ℤ) : Twist F L M n ≃ₗ[F] M :=
  TensorProduct.congr (LinearEquiv.refl F M) (coordinate hL n) ≪≫ₗ TensorProduct.rid F M

@[simp] theorem trivialization_tmul {F : Type u} [Field F] {L : Type v}
    [AddCommGroup L] [Module F L] (hL : Module.finrank F L = 1)
    (M : Type w) [AddCommGroup M] [Module F M] (n : ℤ) (a : M) (t : Power F L n) :
    trivialization hL M n (a ⊗ₜ[F] t) = coordinate hL n t • a := by
  simp [trivialization]

/-- Coordinates commute with tensoring a genuine linear map by the identity. -/
theorem trivialization_map {F : Type u} [Field F] {L : Type v}
    [AddCommGroup L] [Module F L] (hL : Module.finrank F L = 1)
    {M N : Type*} [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (f : M →ₗ[F] N) (n : ℤ) :
    (trivialization hL N n).toLinearMap.comp (TensorProduct.map f LinearMap.id) =
      f.comp (trivialization hL M n).toLinearMap := by
  ext a t
  simp

/-- Multiplication of external Tate powers, in coherent tensor coordinates. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def mul {F : Type u} [Field F] {L : Type v} [AddCommGroup L] [Module F L]
    (hL : Module.finrank F L = 1) (r s : ℤ) :
    Power F L r ⊗[F] Power F L s ≃ₗ[F] Power F L (r + s) :=
  TensorProduct.congr (coordinate hL r) (coordinate hL s) ≪≫ₗ
    TensorProduct.lid F F ≪≫ₗ (coordinate hL (r + s)).symm

/-- Tensoring an external twist with the Tate line raises its external index. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def shift {F : Type u} [Field F] {L : Type v} [AddCommGroup L] [Module F L]
    (hL : Module.finrank F L = 1) (M : Type w) [AddCommGroup M] [Module F M]
    (n : ℤ) : Twist F L M n ⊗[F] L ≃ₗ[F] Twist F L M (n + 1) :=
  TensorProduct.congr (trivialization hL M n) (lineCoordinate hL) ≪≫ₗ
    TensorProduct.rid F M ≪≫ₗ (trivialization hL M (n + 1)).symm

/-- A linear map transported between specified external twists. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def map {F : Type u} [Field F] {L : Type v} [AddCommGroup L] [Module F L]
    (hL : Module.finrank F L = 1) {M : Type w} {N : Type*}
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (f : M →ₗ[F] N) (r s : ℤ) : Twist F L M r →ₗ[F] Twist F L N s :=
  (trivialization hL N s).symm.toLinearMap.comp
    (f.comp (trivialization hL M r).toLinearMap)

/-- Exterior product on fixed external twists, using an actual untwisted map. Coordinate adapter using the chosen Tate coordinates; canonical external
compatibility and coherence are tracked by RL-2195. -/
def tensorMap {F : Type u} [Field F] {L : Type v} [AddCommGroup L] [Module F L]
    (hL : Module.finrank F L = 1) {M N P : Type*}
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    [AddCommGroup P] [Module F P] (f : M ⊗[F] N →ₗ[F] P) (r s : ℤ) :
    Twist F L M r ⊗[F] Twist F L N s →ₗ[F] Twist F L P (r + s) :=
  (trivialization hL P (r + s)).symm.toLinearMap.comp
    (f.comp (TensorProduct.map (trivialization hL M r).toLinearMap
      (trivialization hL N s).toLinearMap))

/-- Tensor powers of a specified scalar-extension equivalence.  The recursion
uses the canonical tensor-product base-change map and the actual given line
map, rather than identifying independently chosen line coordinates. -/
def tensorPowerBaseChangeEquiv
    {F F' L L' : Type*} [Field F] [Field F'] [Algebra F F']
    [AddCommGroup L] [Module F L] [AddCommGroup L'] [Module F' L']
    (e : F' ⊗[F] L ≃ₗ[F'] L') :
    (n : ℕ) → F' ⊗[F] TensorPower F n L ≃ₗ[F'] TensorPower F' n L'
  | 0 => (PiTensorProduct.isEmptyEquiv (R := F) (s := fun _ : Fin 0 ↦ L)
        (Fin 0)).baseChange F F' _ _ ≪≫ₗ
      TensorProduct.AlgebraTensorModule.rid F F' F' ≪≫ₗ
      (PiTensorProduct.isEmptyEquiv (R := F') (s := fun _ : Fin 0 ↦ L') (Fin 0)).symm
  | 1 => (PiTensorProduct.subsingletonEquiv (R := F) (s := fun _ : Fin 1 ↦ L)
        (0 : Fin 1)).baseChange F F' _ _ ≪≫ₗ e ≪≫ₗ
      (PiTensorProduct.subsingletonEquiv (R := F')
        (s := fun _ : Fin 1 ↦ L') (0 : Fin 1)).symm
  | n + 2 =>
      ((TensorPower.mulEquiv (R := F) (M := L) (n := n + 1) (m := 1)).symm).baseChange
          F F' _ _ ≪≫ₗ
        TensorProduct.AlgebraTensorModule.distribBaseChange F F'
          (TensorPower F (n + 1) L) (TensorPower F 1 L) ≪≫ₗ
        TensorProduct.congr (tensorPowerBaseChangeEquiv e (n + 1))
          ((PiTensorProduct.subsingletonEquiv (R := F) (s := fun _ : Fin 1 ↦ L)
              (0 : Fin 1)).baseChange F F' _ _ ≪≫ₗ e ≪≫ₗ
            (PiTensorProduct.subsingletonEquiv (R := F')
              (s := fun _ : Fin 1 ↦ L') (0 : Fin 1)).symm) ≪≫ₗ
        TensorPower.mulEquiv

/-- The recursively constructed comparison commutes with concatenating one
more tensor factor.  Both sides are genuine quotient tensor maps, so the
identity is independent of a presentation as a sum of pure tensors. -/
theorem tensorPowerBaseChangeEquiv_succ_tmul
    {F F' L L' : Type*} [Field F] [Field F'] [Algebra F F']
    [AddCommGroup L] [Module F L] [AddCommGroup L'] [Module F' L']
    (e : F' ⊗[F] L ≃ₗ[F'] L') (n : ℕ) (s : F')
    (a : TensorPower F (n + 1) L) (b : TensorPower F 1 L) :
    tensorPowerBaseChangeEquiv e (n + 2)
        (s ⊗ₜ[F] TensorPower.mulEquiv (n := n + 1) (m := 1) (a ⊗ₜ[F] b)) =
      TensorPower.mulEquiv (n := n + 1) (m := 1)
        (tensorPowerBaseChangeEquiv e (n + 1) (s ⊗ₜ[F] a) ⊗ₜ[F']
          tensorPowerBaseChangeEquiv e 1 (1 ⊗ₜ[F] b)) := by
  simp [tensorPowerBaseChangeEquiv]

/-- The scalar-extension equivalence on the dual Tate line.  Its evaluation
is the scalar extension of evaluation followed by precomposition with `e⁻¹`.
The only finiteness input is the proved rank-one hypothesis. -/
def dualBaseChangeEquiv
    {F F' L L' : Type*} [Field F] [Field F'] [Algebra F F']
    [AddCommGroup L] [Module F L] [AddCommGroup L'] [Module F' L']
    (hL : Module.finrank F L = 1) (e : F' ⊗[F] L ≃ₗ[F'] L') :
    F' ⊗[F] Module.Dual F L ≃ₗ[F'] Module.Dual F' L' := by
  letI : Module.Finite F L := Module.finite_of_finrank_eq_succ hL
  exact (TensorProduct.isBaseChange F L F').toDualBaseChange ≪≫ₗ e.dualMap.symm

/-- The comparison of every external Tate power induced by the given Tate-line
equivalence: tensor powers for nonnegative indices, dual tensor powers for
negative indices.  No auxiliary line coordinate enters this construction. -/
def powerBaseChangeEquiv
    {F F' L L' : Type*} [Field F] [Field F'] [Algebra F F']
    [AddCommGroup L] [Module F L] [AddCommGroup L'] [Module F' L']
    (hL : Module.finrank F L = 1) (e : F' ⊗[F] L ≃ₗ[F'] L') :
    (n : ℤ) → F' ⊗[F] Power F L n ≃ₗ[F'] Power F' L' n
  | .ofNat n => tensorPowerBaseChangeEquiv e n
  | .negSucc n => tensorPowerBaseChangeEquiv (dualBaseChangeEquiv hL e) (n + 1)

/-- External cohomology comparison, induced by the supplied cohomology and
Tate-line comparisons and canonical distribution of scalar extension over a
tensor product. -/
def twistBaseChangeEquiv
    {F F' L L' M M' : Type*} [Field F] [Field F'] [Algebra F F']
    [AddCommGroup L] [Module F L] [AddCommGroup L'] [Module F' L']
    [AddCommGroup M] [Module F M] [AddCommGroup M'] [Module F' M']
    (hL : Module.finrank F L = 1) (e : F' ⊗[F] L ≃ₗ[F'] L')
    (f : F' ⊗[F] M ≃ₗ[F'] M') (n : ℤ) :
    F' ⊗[F] Twist F L M n ≃ₗ[F'] Twist F' L' M' n :=
  TensorProduct.AlgebraTensorModule.distribBaseChange F F' M (Power F L n) ≪≫ₗ
    TensorProduct.congr f (powerBaseChangeEquiv hL e n)

/-- In twist one the induced comparison is exactly the given Tate-line map,
under the canonical identification of a one-fold tensor power with the line. -/
theorem powerBaseChangeEquiv_one_tmul
    {F F' L L' : Type*} [Field F] [Field F'] [Algebra F F']
    [AddCommGroup L] [Module F L] [AddCommGroup L'] [Module F' L']
    (hL : Module.finrank F L = 1) (e : F' ⊗[F] L ≃ₗ[F'] L') (s : F') (t : L) :
    powerBaseChangeEquiv hL e 1
        (s ⊗ₜ[F] (PiTensorProduct.subsingletonEquiv (R := F)
          (s := fun _ : Fin 1 ↦ L) (0 : Fin 1)).symm t) =
      (PiTensorProduct.subsingletonEquiv (R := F')
        (s := fun _ : Fin 1 ↦ L') (0 : Fin 1)).symm (e (s ⊗ₜ[F] t)) := by
  simp [powerBaseChangeEquiv, tensorPowerBaseChangeEquiv]

/-- The external first-twist comparison is the tensor product of the given
cohomology comparison with the given Tate-line comparison. -/
theorem twistBaseChangeEquiv_one_tmul
    {F F' L L' M M' : Type*} [Field F] [Field F'] [Algebra F F']
    [AddCommGroup L] [Module F L] [AddCommGroup L'] [Module F' L']
    [AddCommGroup M] [Module F M] [AddCommGroup M'] [Module F' M']
    (hL : Module.finrank F L = 1) (e : F' ⊗[F] L ≃ₗ[F'] L')
    (f : F' ⊗[F] M ≃ₗ[F'] M') (s : F') (a : M) (t : L) :
    twistBaseChangeEquiv hL e f 1
        (s ⊗ₜ[F] (a ⊗ₜ[F] (PiTensorProduct.subsingletonEquiv (R := F)
          (s := fun _ : Fin 1 ↦ L) (0 : Fin 1)).symm t)) =
      f (s ⊗ₜ[F] a) ⊗ₜ[F']
        (PiTensorProduct.subsingletonEquiv (R := F')
          (s := fun _ : Fin 1 ↦ L') (0 : Fin 1)).symm (e (1 ⊗ₜ[F] t)) := by
  simp only [twistBaseChangeEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.congr_tmul]
  rw [powerBaseChangeEquiv_one_tmul]

/-- The dual comparison is anchored to the scalar extension of evaluation.
This determines its action independently of a basis or representative. -/
theorem dualBaseChangeEquiv_eval
    {F F' L L' : Type*} [Field F] [Field F'] [Algebra F F']
    [AddCommGroup L] [Module F L] [AddCommGroup L'] [Module F' L']
    (hL : Module.finrank F L = 1) (e : F' ⊗[F] L ≃ₗ[F'] L')
    (s : F') (ell : Module.Dual F L) (t : L) :
    dualBaseChangeEquiv hL e (s ⊗ₜ[F] ell) (e (1 ⊗ₜ[F] t)) =
      s * algebraMap F F' (ell t) := by
  letI : Module.Finite F L := Module.finite_of_finrank_eq_succ hL
  simp only [dualBaseChangeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.dualMap_symm, LinearEquiv.dualMap_apply, LinearEquiv.symm_apply_apply]
  exact IsBaseChange.toDualBaseChange_tmul (TensorProduct.isBaseChange F L F') s ell t

end Tate

/-- Canonical projection to one cohomological degree of a single graded total space. -/
def gradeProjection {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    (G : ℤ → Submodule F M) (hG : DirectSum.IsInternal G) (i : ℤ) : M →ₗ[F] G i :=
  (DirectSum.component F ℤ (fun i ↦ G i) i).comp
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap G) hG).symm.toLinearMap

/-- The inclusion of a twisted homogeneous piece into externally twisted total cohomology. -/
def twistedInclusion {F L M : Type*} [Field F] [AddCommGroup L] [Module F L]
    [AddCommGroup M] [Module F M] (G : ℤ → Submodule F M) (i n : ℤ) :
    Tate.Twist F L (G i) n →ₗ[F] Tate.Twist F L M n :=
  TensorProduct.map (G i).subtype LinearMap.id

/-- Extend a trace from the twisted top cohomological degree by zero in all other degrees. -/
def extendTopTrace {F L M : Type*} [Field F] [AddCommGroup L] [Module F L]
    [AddCommGroup M] [Module F M] (G : ℤ → Submodule F M)
    (hG : DirectSum.IsInternal G) (d : ℕ)
    (ell : Tate.Twist F L (G (2 * (d : ℤ))) d →ₗ[F] F) :
    Tate.Twist F L M d →ₗ[F] F :=
  ell.comp (TensorProduct.map (gradeProjection G hG (2 * (d : ℤ))) LinearMap.id)

/-- Contraction permits different modules in its left and right factors. -/
def contractTwistedRight {F M N : Type*} [Field F]
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (ell : N →ₗ[F] F) : M ⊗[F] N →ₗ[F] M :=
  (TensorProduct.rid F M).toLinearMap.comp (TensorProduct.map LinearMap.id ell)

/-- The functional on a Künneth product obtained by transporting the tensor product of
two trace functionals across a bijective Künneth map. -/
noncomputable def tensorProductTrace
    {F : Type u} [Field F] {M : Type v} {N : Type w} {P : Type max v w}
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    [AddCommGroup P] [Module F P]
    (kunnethMap : M ⊗[F] N →ₗ[F] P) (h_kunneth : Function.Bijective kunnethMap)
    (traceM : M →ₗ[F] F) (traceN : N →ₗ[F] F) : P →ₗ[F] F :=
  (TensorProduct.lift ((LinearMap.mul F F).compl₁₂ traceM traceN)).comp
    (LinearEquiv.ofBijective kunnethMap h_kunneth).symm.toLinearMap

/-- The tensor-product trace evaluates on an exterior product as the product of traces. -/
theorem tensorProductTrace_kunnethMap_tmul
    {F : Type u} [Field F] {M : Type v} {N : Type w} {P : Type max v w}
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    [AddCommGroup P] [Module F P]
    (kunnethMap : M ⊗[F] N →ₗ[F] P) (h_kunneth : Function.Bijective kunnethMap)
    (traceM : M →ₗ[F] F) (traceN : N →ₗ[F] F) (x : M) (y : N) :
    tensorProductTrace kunnethMap h_kunneth traceM traceN (kunnethMap (x ⊗ₜ[F] y)) =
      traceM x * traceN y := sorry

/-- Contract the right tensor factor against a linear functional. -/
noncomputable def contractRight
    {F : Type u} [Field F] {M : Type v} [AddCommGroup M] [Module F M]
    (trace : M →ₗ[F] F) : M ⊗[F] M →ₗ[F] M :=
  (TensorProduct.rid F M).toLinearMap.comp (TensorProduct.map LinearMap.id trace)

/-- The canonical interchange of the middle two factors in a fourfold tensor product
for internally graded modules.  The middle swap is the graded Koszul braiding, so
homogeneous tensors acquire `(-1)^(deg right · deg left)` as required by the
graded-commutative cup product. -/
noncomputable def tensorInterchange
    (F : Type u) [Field F] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (GM : ℤ → Submodule F M) (GN : ℤ → Submodule F N)
    (hM : DirectSum.IsInternal GM) (hN : DirectSum.IsInternal GN) :
    (M ⊗[F] N) ⊗[F] (M ⊗[F] N) ≃ₗ[F] (M ⊗[F] M) ⊗[F] (N ⊗[F] N) := by
  let dM : M ≃ₗ[F] (⨁ i, GM i) :=
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap GM) hM).symm
  let dN : N ≃ₗ[F] (⨁ i, GN i) :=
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap GN) hN).symm
  let gradedRightComm :
      (((⨁ i, GM i) ⊗[F] (⨁ i, GN i)) ⊗[F] (⨁ i, GM i)) ≃ₗ[F]
        (((⨁ i, GM i) ⊗[F] (⨁ i, GM i)) ⊗[F] (⨁ i, GN i)) :=
    TensorProduct.assoc F (⨁ i, GM i) (⨁ i, GN i) (⨁ i, GM i) ≪≫ₗ
      TensorProduct.congr (LinearEquiv.refl F (⨁ i, GM i))
        ((@TensorProduct.gradedComm F ℤ _ _ _ (fun i => GN i) (fun i => GM i) _ _ _ _ _) :
          ((⨁ i, GN i) ⊗[F] (⨁ i, GM i)) ≃ₗ[F]
            ((⨁ i, GM i) ⊗[F] (⨁ i, GN i))) ≪≫ₗ
      (TensorProduct.assoc F (⨁ i, GM i) (⨁ i, GM i) (⨁ i, GN i)).symm
  exact
    TensorProduct.congr
        (TensorProduct.congr dM dN) (TensorProduct.congr dM dN) ≪≫ₗ
      (TensorProduct.assoc F ((⨁ i, GM i) ⊗[F] (⨁ i, GN i))
          (⨁ i, GM i) (⨁ i, GN i)).symm ≪≫ₗ
      TensorProduct.congr gradedRightComm (LinearEquiv.refl F (⨁ i, GN i)) ≪≫ₗ
      TensorProduct.assoc F ((⨁ i, GM i) ⊗[F] (⨁ i, GM i))
        (⨁ i, GN i) (⨁ i, GN i) ≪≫ₗ
      TensorProduct.congr
        (TensorProduct.congr dM.symm dM.symm)
        (TensorProduct.congr dN.symm dN.symm)

/-- The graded interchange on homogeneous tensors has precisely the sign from
moving the second factor past the third. -/
theorem tensorInterchange_tmul
    (F : Type u) [Field F] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N]
    (GM : ℤ → Submodule F M) (GN : ℤ → Submodule F N)
    (hM : DirectSum.IsInternal GM) (hN : DirectSum.IsInternal GN)
    {i j k l : ℤ} (a : GM i) (b : GN j) (c : GM k) (d : GN l) :
    tensorInterchange F GM GN hM hN
        (((a : M) ⊗ₜ[F] (b : N)) ⊗ₜ[F] ((c : M) ⊗ₜ[F] (d : N))) =
      (-1 : ℤˣ) ^ (k * j) •
        (((a : M) ⊗ₜ[F] (c : M)) ⊗ₜ[F] ((b : N) ⊗ₜ[F] (d : N))) := by
  have hMc (p : ℤ) (x : GM p) :
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap GM) hM).symm (x : M) =
        DirectSum.lof F ℤ (fun p ↦ GM p) p x := by
    apply (LinearEquiv.ofBijective (DirectSum.coeLinearMap GM) hM).symm_apply_eq.mpr
    exact (DirectSum.coeLinearMap_lof GM p x).symm
  have hNc (p : ℤ) (x : GN p) :
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap GN) hN).symm (x : N) =
        DirectSum.lof F ℤ (fun p ↦ GN p) p x := by
    apply (LinearEquiv.ofBijective (DirectSum.coeLinearMap GN) hN).symm_apply_eq.mpr
    exact (DirectSum.coeLinearMap_lof GN p x).symm
  simp [tensorInterchange, hMc, hNc, TensorProduct.gradedComm_of_tmul_of,
    Units.smul_def, TensorProduct.smul_tmul', TensorProduct.tmul_smul]

end WeilCohomology
