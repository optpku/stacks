module

public import ReasLib.RingTheory.Module.Support.PrimeSpan.LinearMap
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v w

namespace LinearMap

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N]

/- Lemma 42.68.41 (1): for equal-length prime-span filtrations of finite modules over a
Noetherian local ring, a linear map is injective exactly when its localization at the prime is
bijective. -/
@[stacks 02QB]
#check (LinearMap.injective_iff_isBijectiveAt_of_spanFiltrations :
  ∀ (q : PrimeSpectrum R) (hdim : ringKrullDim (R ⧸ q.asIdeal) = 1)
    {l : ℕ} (x : Fin l → M) (y : Fin l → N) (φ : M →ₗ[R] N)
    (hx_span : Submodule.span R (Set.range x) = ⊤)
    (hx_factors : ∀ i : Fin l,
      Nonempty
        ((Submodule.span R (x '' Set.Iic i) ⧸
            (Submodule.span R (x '' Set.Iio i)).submoduleOf
              (Submodule.span R (x '' Set.Iic i))) ≃ₗ[R]
          R ⧸ q.asIdeal))
    (hy_span : Submodule.span R (Set.range y) = ⊤)
    (hy_factors : ∀ i : Fin l,
      Nonempty
        ((Submodule.span R (y '' Set.Iic i) ⧸
            (Submodule.span R (y '' Set.Iio i)).submoduleOf
              (Submodule.span R (y '' Set.Iic i))) ≃ₗ[R]
          R ⧸ q.asIdeal)),
    Function.Injective φ ↔ φ.IsBijectiveAt q)

/- Lemma 42.68.41 (2): if the map is injective and its localized image determinant differs
from the target determinant by `f`, then the cokernel length is the order of vanishing of `f`. -/
@[stacks 02QB]
#check (LinearMap.cokernelLength_eq_ordFrac_of_spanFiltrations :
  ∀ (q : PrimeSpectrum R) (hdim : ringKrullDim (R ⧸ q.asIdeal) = 1)
    {l : ℕ} (x : Fin l → M) (y : Fin l → N) (φ : M →ₗ[R] N)
    (hx_span : Submodule.span R (Set.range x) = ⊤)
    (hx_factors : ∀ i : Fin l,
      Nonempty
        ((Submodule.span R (x '' Set.Iic i) ⧸
            (Submodule.span R (x '' Set.Iio i)).submoduleOf
              (Submodule.span R (x '' Set.Iic i))) ≃ₗ[R]
          R ⧸ q.asIdeal))
    (hy_span : Submodule.span R (Set.range y) = ⊤)
    (hy_factors : ∀ i : Fin l,
      Nonempty
        ((Submodule.span R (y '' Set.Iic i) ⧸
            (Submodule.span R (y '' Set.Iio i)).submoduleOf
              (Submodule.span R (y '' Set.Iic i))) ≃ₗ[R]
          R ⧸ q.asIdeal))
    (hφ : Function.Injective φ) (f : q.asIdeal.ResidueField)
    (hdet : Module.PrimeSpan.mapSymbol q φ x y hx_span hx_factors hy_span hy_factors =
      f • Module.PrimeSpan.symbol q y hy_span hy_factors),
    -- Local instance justification (proof-local temporary data): hdim supplies the dimension bound required by Ring.ordFrac without exposing a redundant class assumption.
    letI : Ring.KrullDimLE 1 (R ⧸ q.asIdeal) :=
      (Ring.krullDimLE_iff).2 (hdim.le.trans_eq rfl)
    ((Module.length R (N ⧸ φ.range)).toNat : ℤ) =
      WithZero.log (Ring.ordFrac (R ⧸ q.asIdeal) f))

end LinearMap
