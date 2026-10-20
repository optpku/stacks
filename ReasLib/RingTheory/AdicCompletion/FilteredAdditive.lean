module
public import Mathlib.RingTheory.AdicCompletion.Functoriality

@[expose] public section
universe u v
namespace FilteredAdditiveCompletion

variable {R S M N : Type u} [CommRing R] [CommRing S]
variable [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
variable (I : Ideal R) (J : Ideal S) (f : M →+ N)
variable (hf : ∀ n (x : M), x ∈ (I ^ n • (⊤ : Submodule R M)) →
  f x ∈ (J ^ n • (⊤ : Submodule S N)))

/-- A filtration-preserving additive map induces maps of additive quotients.
Only integer linearity is used; no false R- or S-linearity is asserted. -/
def quotientMap (n : ℕ) :
    M ⧸ (I ^ n • (⊤ : Submodule R M)) →+
      N ⧸ (J ^ n • (⊤ : Submodule S N)) :=
  (((I ^ n • (⊤ : Submodule R M)).restrictScalars ℤ).mapQ
    ((J ^ n • (⊤ : Submodule S N)).restrictScalars ℤ)
    f.toIntLinearMap (hf n)).toAddMonoidHom

/-- Quotient maps commute with transition maps because both send a
representative x to the class of f(x). -/
theorem quotientMap_transition {m n : ℕ} (h : m ≤ n)
    (x : M ⧸ (I ^ n • (⊤ : Submodule R M))) :
    AdicCompletion.transitionMap J N h (quotientMap I J f hf n x) =
      quotientMap I J f hf m (AdicCompletion.transitionMap I M h x) := by
  induction x using Quotient.inductionOn' with
  | h x => rfl

/-- Complete an actual filtration-preserving additive map componentwise.
The resulting map is additive, not falsely linear over the envelope ring. -/
def map : AdicCompletion I M →+ AdicCompletion J N where
  toFun x := ⟨fun n ↦ quotientMap I J f hf n (x.val n), by
    intro m n h
    rw [quotientMap_transition, x.property h]⟩
  map_zero' := by
    apply Subtype.ext
    funext n
    exact map_zero (quotientMap I J f hf n)
  map_add' x y := by
    apply Subtype.ext
    funext n
    exact map_add (quotientMap I J f hf n) (x.val n) (y.val n)

/-- Every additive map preserves the p-power filtration: multiplying by a
natural number is repeated addition, independently of the ambient ring. -/
theorem preserves_powers (p : ℕ) (n : ℕ) (x : M)
    (hx : x ∈ (Ideal.span {(p : R)}) ^ n • (⊤ : Submodule R M)) :
    f x ∈ (Ideal.span {(p : S)}) ^ n • (⊤ : Submodule S N) := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at hx ⊢
  obtain ⟨y, _, rfl⟩ := hx
  refine ⟨f y, Submodule.mem_top, ?_⟩
  simp [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

/-- The canonical p-adic extension of any additive map. -/
def pAdicMap (p : ℕ) :
    AdicCompletion (Ideal.span {(p : R)}) M →+
      AdicCompletion (Ideal.span {(p : S)}) N :=
  map (Ideal.span {(p : R)}) (Ideal.span {(p : S)}) f
    (preserves_powers f p)

end FilteredAdditiveCompletion
