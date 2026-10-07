module

public import ReasLib.Algebra.CentralSimple.SimpleModule.Uniqueness
public import ReasLib.Algebra.CentralSimple.SimpleModule.DirectSum
public import ReasLib.Algebra.CentralSimple.SimpleModule.DoubleCentralizer
public import ReasLib.Algebra.CentralSimple.SimpleModule.Existence
public import ReasLib.Algebra.CentralSimple.Basic
public import ReasLib.Algebra.CentralSimple.SimpleModule.DirectSum
public import ReasLib.Algebra.CentralSimple.SimpleModule.DoubleCentralizer
public import ReasLib.Algebra.CentralSimple.SimpleModule.Existence
public import ReasLib.Algebra.CentralSimple.Basic
public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.Algebra.Central.Matrix
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-! # The Skolem-Noether Theorem

The Skolem-Noether theorem states that any two k-algebra homomorphisms from a simple
k-algebra B into a finite central simple k-algebra A are conjugate by a unit of A.
As a corollary, every k-algebra automorphism of a finite central simple k-algebra is
inner (i.e., given by conjugation by a unit).

## Main declarations

- `CSA.skolemNoether` — any two k-algebra maps f g : B →ₐ[k] A are conjugate by a unit
- `CSA.autInner` — every automorphism of a finite CSA is a conjugation automorphism
- `CSA.autInner_apply` — the conjugation automorphism acts by x * a * x⁻¹
- `CSA.algEquiv_isInner` — pointwise form: ∃ x, ∀ a, σ a = x * a * x⁻¹
- `CSA.matrix_algEquiv_isInner` — specialization to matrix algebras

## References

- [Stacks Project, Tag 074Q](https://stacks.math.columbia.edu/tag/074Q)
- [Stacks Project, Tag 074R](https://stacks.math.columbia.edu/tag/074R)

@stack 074Q
@stack 074R
-/

set_option maxHeartbeats 400000
@[expose] public section

universe u v w

namespace CSA

open ConjAct
open scoped TensorProduct

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)
variable {B : Type w} [Ring B] [Algebra k B] [IsSimpleRing B]

/-- A simple k-algebra mapping into a finite-dimensional k-algebra is itself
finite-dimensional. -/
private lemma simple_source_algHom_finiteDimensional (h : B →ₐ[k] A) :
    FiniteDimensional k B :=
  FiniteDimensional.of_injective h.toLinearMap (RingHom.injective h.toRingHom)

section

omit [IsSimpleRing B] in
/-- The action of B on a left A-module induced by an algebra map commutes with every
A-linear endomorphism. -/
private lemma tensor_action_commutes {M : Type*} [AddCommGroup M] [Module A M]
    (h : B →ₐ[k] A) (b : B) (l : Module.End A M) (m : M) :
    (h b : A) • (l m) = l ((h b : A) • m) := by
  simpa using (l.map_smul (h b) m).symm

end

/-- Every finite-dimensional nontrivial k-algebra admits a simple left submodule of its
regular module. -/
private theorem exists_simple_regular_submodule
    {R : Type v} [Ring R] [Algebra k R] [FiniteDimensional k R] [Nontrivial R] :
    ∃ M : Submodule R R, IsSimpleModule R M := by
  simpa using FiniteDimensional.exists_simpleSubmodule_regular (k := k) (A := R)

/-- A simple left module over the finite-dimensional algebra A is finite dimensional
over k. -/
private theorem simple_module_finite_dimensional
    {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [IsSimpleModule A M] :
    FiniteDimensional k M := by
  simpa using IsSimpleModule.finiteDimensional (k := k) (A := A) (M := M)

/-- Under the double-centralizer equivalence, an element of A acts on M by the original
scalar action. -/
private theorem simple_module_double_centralizer_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (a : A) (m : M) :
    IsSimpleModule.doubleCentralizerAlgEquiv (k := k) (A := A) (M := M) a m = a • m := by
  rfl

/-- Under the double-centralizer equivalence, multiplication in A acts by composition
on M. -/
private theorem simple_module_double_centralizer_mul_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (a b : A) (m : M) :
    IsSimpleModule.doubleCentralizerAlgEquiv (k := k) (A := A) (M := M) (a * b) m =
      a • (IsSimpleModule.doubleCentralizerAlgEquiv (k := k) (A := A) (M := M) b m) := by
  have hmul :=
    congrArg (fun f : Module.End (Module.End A M) M ↦ f m)
      ((IsSimpleModule.doubleCentralizerAlgEquiv (k := k) (A := A) (M := M)).map_mul a b)
  simpa [simple_module_double_centralizer_apply] using hmul

/-- If the endomorphism ring of a nonzero module is central over k, then the coefficient
division ring is central over k as well. -/
private theorem endomorphism_ring_isCentral_of_central
    {D : Type v} {M : Type v} [DivisionRing D] [AddCommGroup M] [Module D M] [Nontrivial M]
    [Algebra k D] [Module k M] [IsScalarTower k D M]
    [Algebra.IsCentral k (Module.End D M)] :
    Algebra.IsCentral k D := by
  sorry
/-- If L = Module.End A M for a simple A-module M, then L is central over k whenever A
is central over k. -/
private theorem moduleEnd_isCentral
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] [Algebra.IsCentral k A] :
    Algebra.IsCentral k (Module.End A M) := by
  sorry
/-- The algebra map h : B →ₐ[k] A induces a left B-action on the simple A-module M. -/
private noncomputable def algHom_action_to_End
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A) :
    B →ₐ[k] Module.End k M :=
  { toFun := fun b ↦
      { toFun := fun m ↦ (h b : A) • m
        map_add' := fun m n ↦ smul_add (h b : A) m n
        map_smul' := fun c m ↦ by
          simpa [smul_assoc] using (smul_comm (h b : A) c m) }
    map_one' := by
      ext m
      simp
    map_mul' := by
      intro b₁ b₂
      ext m
      simp [mul_smul]
    map_zero' := by
      ext m
      simp
    map_add' := by
      intro b₁ b₂
      ext m
      simp [add_smul]
    commutes' := by
      intro c
      ext m
      simp }

/-- Every A-linear endomorphism of M is naturally k-linear. -/
private noncomputable def moduleEnd_action_to_End
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    Module.End A M →ₐ[k] Module.End k M :=
  { toFun := fun l ↦ LinearMap.restrictScalars k l
    map_one' := rfl
    map_mul' := fun _ _ ↦ rfl
    map_zero' := rfl
    map_add' := fun _ _ ↦ rfl
    commutes' := by
      intro c
      ext m
      simp [Algebra.algebraMap_eq_smul_one] }

/-- The commuting B- and End_A(M)-actions on M induce the canonical tensor-product action. -/
private noncomputable def tensor_product_action_to_End
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A) :
    TensorProduct k B (Module.End A M) →ₐ[k] Module.End k M :=
  Algebra.TensorProduct.lift
    (algHom_action_to_End (k := k) (A := A) h)
    (moduleEnd_action_to_End (k := k) (A := A))
    (fun b l ↦ by
      ext m
      change (h b : A) • l m = l ((h b : A) • m)
      exact tensor_action_commutes (A := A) h b l m)

omit [IsSimpleRing B] in
/-- On a pure tensor, the tensor-product action is m ↦ l ((h b) • m). -/
private theorem tensor_product_action_to_End_tmul_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A)
    (b : B) (l : Module.End A M) (m : M) :
    tensor_product_action_to_End (k := k) (A := A) h (b ⊗ₜ[k] l) m =
      l ((h b : A) • m) := by
  simp [tensor_product_action_to_End, algHom_action_to_End, moduleEnd_action_to_End]

/-- A reducible wrapper for each algebra map h : B →ₐ[k] A so the two tensor-product module
structures live on different Lean types. -/
private noncomputable abbrev TensorTwist
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (_h : B →ₐ[k] A) : Type v :=
  M

/-- The R := B ⊗[k] Module.End A M-module structure on the wrapped copy of M induced by h. -/
private noncomputable abbrev tensor_twist_module
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A) :
    Module (TensorProduct k B (Module.End A M)) (TensorTwist (A := A) (B := B) (M := M) h) :=
  Module.compHom (TensorTwist (A := A) (B := B) (M := M) h)
    (tensor_product_action_to_End (k := k) (A := A) (B := B) (M := M) h).toRingHom

/-- The wrapped copy TensorTwist h carries the canonical tensor product module structure. -/
private noncomputable instance tensor_twist_module_inst
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A) :
    Module (TensorProduct k B (Module.End A M)) (TensorTwist (A := A) (B := B) (M := M) h) :=
  tensor_twist_module (k := k) (A := A) (B := B) (M := M) h

omit [IsSimpleRing B] in
/-- The wrapped R-module is compatible with the original k-vector-space structure on M. -/
private theorem tensor_twist_isScalarTower
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A) :
    IsScalarTower k (TensorProduct k B (Module.End A M))
      (TensorTwist (A := A) (B := B) (M := M) h) := by
  sorry
/-- On a pure tensor, the wrapped R-action attached to h is still m ↦ l ((h b) • m). -/
private theorem tensor_twist_tmul_smul_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A)
    (b : B) (l : Module.End A M) (m : TensorTwist (A := A) (B := B) (M := M) h) :
    letI : Module (TensorProduct k B (Module.End A M))
        (TensorTwist (A := A) (B := B) (M := M) h) :=
      tensor_twist_module (k := k) (A := A) (B := B) (M := M) h
    ((b ⊗ₜ[k] l : TensorProduct k B (Module.End A M)) • m) = l ((h b : A) • m) := by
  sorry
/-- The left tensor generator acts on the wrapped module through the original B-action. -/
private theorem tensor_twist_includeLeft_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A)
    (b : B) (m : TensorTwist (A := A) (B := B) (M := M) h) :
    letI : Module (TensorProduct k B (Module.End A M))
        (TensorTwist (A := A) (B := B) (M := M) h) :=
      tensor_twist_module (k := k) (A := A) (B := B) (M := M) h
    ((Algebra.TensorProduct.includeLeft :
        B →ₐ[k] TensorProduct k B (Module.End A M)) b) • m =
      (h b : A) • m := by
  dsimp [tensor_twist_module, TensorTwist]
  simpa [Algebra.TensorProduct.includeLeft_apply] using
    tensor_twist_tmul_smul_apply (k := k) (A := A) (B := B) (M := M) h b
      (1 : Module.End A M) m

omit [IsSimpleRing B] in
/-- The right tensor generator acts on the wrapped module by evaluation of Module.End A M. -/
private theorem tensor_twist_includeRight_apply
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] (h : B →ₐ[k] A)
    (l : Module.End A M) (m : TensorTwist (A := A) (B := B) (M := M) h) :
    letI : Module (TensorProduct k B (Module.End A M))
        (TensorTwist (A := A) (B := B) (M := M) h) :=
      tensor_twist_module (k := k) (A := A) (B := B) (M := M) h
    ((Algebra.TensorProduct.includeRight :
        Module.End A M →ₐ[k] TensorProduct k B (Module.End A M)) l) • m = l m := by
  sorry




omit [IsSimpleRing B] in
/-- The wrapped R-module is finite because its underlying k-vector space is still M. -/
private theorem tensor_twist_module_finite
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] (h : B →ₐ[k] A)
    [Module (TensorProduct k B (Module.End A M))
      (TensorTwist (A := A) (B := B) (M := M) h)]
    [IsScalarTower k (TensorProduct k B (Module.End A M))
      (TensorTwist (A := A) (B := B) (M := M) h)] :
    Module.Finite (TensorProduct k B (Module.End A M))
      (TensorTwist (A := A) (B := B) (M := M) h) := by
  let R := TensorProduct k B (Module.End A M)
  letI : FiniteDimensional k (TensorTwist (A := A) (B := B) (M := M) h) := by
    simpa [TensorTwist]
  exact Module.Finite.of_restrictScalars_finite k R (TensorTwist (A := A) (B := B) (M := M) h)

omit [IsSimpleRing B] in
/-- An R-linear equivalence between the g- and f-twists already commutes with the
right-factor action of Module.End A M. -/
private theorem intertwiner_restricts_to_moduleEnd_map_smul
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M]
    (f g : B →ₐ[k] A)
    (φ :
      TensorTwist (A := A) (B := B) (M := M) g ≃ₗ[TensorProduct k B (Module.End A M)]
        TensorTwist (A := A) (B := B) (M := M) f) :
    ∀ l : Module.End A M, ∀ m : M, φ (l • m) = l • φ m := by
  intro l m
  let m' : TensorTwist (A := A) (B := B) (M := M) g := m
  change φ (l m') = l (φ m')
  have hsmul :=
    φ.map_smul
      ((Algebra.TensorProduct.includeRight :
          Module.End A M →ₐ[k] TensorProduct k B (Module.End A M)) l) m'
  calc
    φ (l m') = φ (((Algebra.TensorProduct.includeRight :
        Module.End A M →ₐ[k] TensorProduct k B (Module.End A M)) l) • m') := by
      rw [(tensor_twist_includeRight_apply (k := k) (A := A) (B := B) (M := M) g l m').symm]
    _ = ((Algebra.TensorProduct.includeRight :
        Module.End A M →ₐ[k] TensorProduct k B (Module.End A M)) l) • φ m' := hsmul
    _ = l (φ m') := by
      rw [tensor_twist_includeRight_apply (k := k) (A := A) (B := B) (M := M) f l (φ m')]

/-- An R-linear equivalence between the two twists becomes an L-linear automorphism of the
underlying simple A-module M. -/
private noncomputable def intertwiner_restricts_to_moduleEnd
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M]
    (f g : B →ₐ[k] A)
    (φ :
      TensorTwist (A := A) (B := B) (M := M) g ≃ₗ[TensorProduct k B (Module.End A M)]
        TensorTwist (A := A) (B := B) (M := M) f) :
    M ≃ₗ[Module.End A M] M :=
  { toFun := φ
    invFun := φ.symm
    left_inv := φ.left_inv
    right_inv := φ.right_inv
    map_add' := φ.map_add
    map_smul' := intertwiner_restricts_to_moduleEnd_map_smul
      (k := k) (A := A) (B := B) (M := M) f g φ }

omit [IsSimpleRing B] in
/-- An R-linear equivalence between the two twists produces the conjugating unit in A. -/
private theorem intertwiner_to_conjugating_unit
    {M : Type v} [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M]
    (f g : B →ₐ[k] A)
    (φ :
      TensorTwist (A := A) (B := B) (M := M) g ≃ₗ[TensorProduct k B (Module.End A M)]
        TensorTwist (A := A) (B := B) (M := M) f) :
    ∃ x : Aˣ,
      f = (MulSemiringAction.toAlgEquiv k A (toConjAct x)).toAlgHom.comp g := by
  sorry
/-- If A and A' are simple k-algebras and one of them is finite-dimensional and central
over k, then the tensor product A ⊗[k] A' is simple. -/
private theorem isSimpleRing_tensorProduct_of_finite_central_factor
    {A₁ : Type*} {A₂ : Type*} [Ring A₁] [Ring A₂] [Algebra k A₁] [Algebra k A₂]
    [IsSimpleRing A₁] [IsSimpleRing A₂]
    (h : (FiniteDimensional k A₁ ∧ Algebra.IsCentral k A₁) ∨
      (FiniteDimensional k A₂ ∧ Algebra.IsCentral k A₂)) :
    IsSimpleRing (A₁ ⊗[k] A₂) := by
  rcases h with h | h
  · letI := h.1
    letI := h.2
    exact isSimpleRing_tensorProduct_of_finite_central_left_factor (k := k)
  · letI := h.1
    letI := h.2
    let h' : IsSimpleRing (A₂ ⊗[k] A₁) :=
      isSimpleRing_tensorProduct_of_finite_central_left_factor (k := k)
    exact IsSimpleRing.of_ringEquiv (Algebra.TensorProduct.comm k A₂ A₁).toRingEquiv h'

/-- **Skolem-Noether theorem**: if A is a finite central simple k-algebra, B is a simple
k-algebra, and f g : B →ₐ[k] A are k-algebra homomorphisms, then f and g are conjugate
by a unit of A. -/
@[stacks 074Q]
theorem skolemNoether (f g : B →ₐ[k] A) :
    ∃ x : Aˣ,
      f = (MulSemiringAction.toAlgEquiv k A (toConjAct x)).toAlgHom.comp g := by
  sorry

section

variable {A' : CSA.{u, v} k}

/-- Every automorphism of a finite central simple algebra is conjugation by a unit. -/
theorem autInner (σ : A' ≃ₐ[k] A') :
    ∃ x : A'ˣ, σ = MulSemiringAction.toAlgEquiv k A' (toConjAct x) := by
  rcases A'.skolemNoether σ.toAlgHom (AlgHom.id k A') with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  ext a
  simpa [AlgHom.comp_apply] using DFunLike.congr_fun hx a

/-- The canonical conjugation automorphism acts by x * a * x⁻¹. -/
lemma autInner_apply (x : A'ˣ) (a : A') :
    MulSemiringAction.toAlgEquiv k A' (toConjAct x) a = ↑x * a * ↑(x⁻¹) := by
  simp [ConjAct.units_smul_def]

/-- **Skolem-Noether corollary**: any k-algebra automorphism of a finite central simple
k-algebra is inner. -/
@[stacks 074R]
theorem algEquiv_isInner (σ : A' ≃ₐ[k] A') :
    ∃ x : A'ˣ, ∀ a : A', σ a = ↑x * a * ↑(x⁻¹) := by
  rcases autInner σ with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  intro a
  rw [hx]
  simpa using autInner_apply (k := k) x a

/-- Every k-algebra automorphism of a full matrix algebra over a field is inner. -/
theorem matrix_algEquiv_isInner (n : ℕ)
    (σ : Matrix (Fin n) (Fin n) k ≃ₐ[k] Matrix (Fin n) (Fin n) k) :
    ∃ x : (Matrix (Fin n) (Fin n) k)ˣ,
      ∀ M : Matrix (Fin n) (Fin n) k,
        σ M = (x : Matrix (Fin n) (Fin n) k) * M * (↑(x⁻¹) : Matrix (Fin n) (Fin n) k) := by
  cases n with
  | zero =>
      refine ⟨1, fun M ↦ ?_⟩
      exact Subsingleton.elim _ _
  | succ n =>
      let A : CSA.{u, u} k := .mk (AlgCat.of k (Matrix (Fin (n + 1)) (Fin (n + 1)) k))
      change A ≃ₐ[k] A at σ
      simpa [A] using algEquiv_isInner σ

end

end CSA

end
