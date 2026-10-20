module

public import ReasLib.LinearAlgebra.Matrix.ScalarInverse
public import ReasLib.LinearAlgebra.LinearMap.ScalarInverse
import StacksCheckRecall

/-!
The algebra below applies on finite locally free trivializations of the crystal
in Definition 60.26.2. A bounded rank permits one exponent across all such
trivializations, without requiring a global basis. No finite locally free
realization is asserted for an arbitrary categorical `FrobeniusCrystal`.

The unexplained `det(M)` in the source calculation is read as `det(K)`,
consistent with the determinant product identity.
-/

universe u v w x

/- Remark 60.26.3 (1): the determinant product of a scalar inverse pair. -/
@[stacks 07N4] #check (Matrix.detProduct_eq_pow :
  ∀ {R : Type u} [CommRing R] (p r i : ℕ)
    (K L : Matrix (Fin r) (Fin r) R)
    (hKL : K * L = ((p : R) ^ i) • (1 : Matrix (Fin r) (Fin r) R)),
    K.det * L.det = (p : R) ^ (r * i))

/- Remark 60.26.3 (2): the explicit rescaled matrix is a two-sided scalar inverse. -/
@[stacks 07N4] #check (Matrix.powerTwoSided_of_mul_eq :
  ∀ {R : Type u} [CommRing R] (p r i : ℕ)
    (K L : Matrix (Fin r) (Fin r) R)
    (hKL : K * L = ((p : R) ^ i) • (1 : Matrix (Fin r) (Fin r) R)),
    let K' : Matrix (Fin r) (Fin r) R := ((p : R) ^ (r * i)) • K
    let j : ℕ := r * i + i
    K' * L = ((p : R) ^ j) • (1 : Matrix (Fin r) (Fin r) R) ∧
      L * K' = ((p : R) ^ j) • (1 : Matrix (Fin r) (Fin r) R))

/- Remark 60.26.3 (3): one power annihilates the actual kernel and cokernel. -/
@[stacks 07N4] #check (LinearMap.exists_commonPower_annihilating_kernel_cokernel :
  ∀ {R : Type u} [CommRing R]
    {M : Type v} {M' : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (p i r : ℕ) (e : Module.Basis (Fin r) R M) (e' : Module.Basis (Fin r) R M')
    (f : M →ₗ[R] M') (v : M' →ₗ[R] M)
    (hfv : v.comp f = ((p : R) ^ i) • (LinearMap.id : M →ₗ[R] M)),
    ∃ j : ℕ,
      (Ideal.span ({(p : R)} : Set R)) ^ j ≤ Module.annihilator R f.ker ∧
        (Ideal.span ({(p : R)} : Set R)) ^ j ≤
          Module.annihilator R (M' ⧸ f.range))

/- Remark 60.26.3 (4): every prescribed sufficiently large exponent rescales the
reverse map to satisfy both composition identities. -/
@[stacks 07N4] #check (LinearMap.scaledV_comp :
  ∀ {R : Type u} [CommRing R]
    {M : Type v} {M' : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (p i r N : ℕ) (e : Module.Basis (Fin r) R M) (e' : Module.Basis (Fin r) R M')
    (f : M →ₗ[R] M') (v : M' →ₗ[R] M)
    (hfv : v.comp f = ((p : R) ^ i) • (LinearMap.id : M →ₗ[R] M))
    (hN : r * i < N),
    (((p : R) ^ N) • v).comp f =
        ((p : R) ^ (N + i)) • (LinearMap.id : M →ₗ[R] M) ∧
      f.comp (((p : R) ^ N) • v) =
        ((p : R) ^ (N + i)) • (LinearMap.id : M' →ₗ[R] M'))

/- Remark 60.26.3 (5): a common rank bound permits the same explicit rescaling
on all local trivializations, with varying rings and ranks. -/
@[stacks 07N4] #check (LinearMap.scaledV_comp_of_boundedRank :
  ∀ {T : Type x} {R : T → Type u} [∀ t, CommRing (R t)]
    {M : T → Type v} {M' : T → Type w}
    [∀ t, AddCommGroup (M t)] [∀ t, Module (R t) (M t)]
    [∀ t, AddCommGroup (M' t)] [∀ t, Module (R t) (M' t)]
    (p i bound N : ℕ) (r : T → ℕ)
    (e : ∀ t, Module.Basis (Fin (r t)) (R t) (M t))
    (e' : ∀ t, Module.Basis (Fin (r t)) (R t) (M' t))
    (f : ∀ t, M t →ₗ[R t] M' t) (v : ∀ t, M' t →ₗ[R t] M t)
    (hr : ∀ t, r t ≤ bound)
    (hfv : ∀ t, (v t).comp (f t) = ((p : R t) ^ i) • (LinearMap.id : M t →ₗ[R t] M t))
    (hN : bound * i < N),
    ∀ t, (((p : R t) ^ N) • v t).comp (f t) =
          ((p : R t) ^ (N + i)) • (LinearMap.id : M t →ₗ[R t] M t) ∧
      (f t).comp (((p : R t) ^ N) • v t) =
        ((p : R t) ^ (N + i)) • (LinearMap.id : M' t →ₗ[R t] M' t))

/- Remark 60.26.3 (6): a single exponent annihilates every local kernel and
cokernel in a bounded-rank family. -/
@[stacks 07N4] #check (LinearMap.exists_commonPower_annihilating_kernel_cokernel_of_boundedRank :
  ∀ {T : Type x} {R : T → Type u} [∀ t, CommRing (R t)]
    {M : T → Type v} {M' : T → Type w}
    [∀ t, AddCommGroup (M t)] [∀ t, Module (R t) (M t)]
    [∀ t, AddCommGroup (M' t)] [∀ t, Module (R t) (M' t)]
    (p i bound : ℕ) (r : T → ℕ)
    (e : ∀ t, Module.Basis (Fin (r t)) (R t) (M t))
    (e' : ∀ t, Module.Basis (Fin (r t)) (R t) (M' t))
    (f : ∀ t, M t →ₗ[R t] M' t) (v : ∀ t, M' t →ₗ[R t] M t)
    (hr : ∀ t, r t ≤ bound)
    (hfv : ∀ t, (v t).comp (f t) = ((p : R t) ^ i) • (LinearMap.id : M t →ₗ[R t] M t)),
    ∃ j : ℕ, ∀ t,
      (Ideal.span ({(p : R t)} : Set (R t))) ^ j ≤ Module.annihilator (R t) (f t).ker ∧
        (Ideal.span ({(p : R t)} : Set (R t))) ^ j ≤
          Module.annihilator (R t) (M' t ⧸ (f t).range))
