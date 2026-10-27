/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.ResidueField.LocalFiber
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable (p : Ideal R) [p.IsPrime] (qbar : Ideal (p.Fiber S)) [qbar.IsPrime]
variable (q : Ideal S) [q.IsPrime] [q.LiesOver p]

-- Local instance justification (defeq pin): Pin the tensor factor to Localization.localRingHom; priority 100 preserves the existing R_p-algebra on the localized fiber.
attribute [local instance 100] Localization.AtPrime.algebraOfLiesOver

/- Remark (0H9M): for the corresponding primes, the localized fibre
F_qbar is canonically isomorphic over R_p to S_q ⊗[R_p] κ(p), where q is the
contraction along Algebra.TensorProduct.includeRight. Mathlib writes the fibre
as κ(p) ⊗[R] S, canonically symmetric to the source's S ⊗[R] κ(p). -/
@[stacks 0H9M] #check (Ideal.Fiber.localizationEquivTensor p qbar :
  Localization.AtPrime qbar ≃ₐ[Localization.AtPrime p]
    (Localization.AtPrime
      (qbar.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S))
        ⊗[Localization.AtPrime p] p.ResidueField))

/- S_q ⊗[R_p] κ(p) is canonically isomorphic over R_p
to S_q / pS_q. -/
#check (Ideal.Fiber.tensorResidueEquivQuotient p q :
  (Localization.AtPrime q ⊗[Localization.AtPrime p] p.ResidueField) ≃ₐ[Localization.AtPrime p]
    (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))))

/- The first comparison identifies the localization map
with the canonical tensor map, sending k ⊗ₜ[R] s to the localized image of s
tensored with k over R_p. -/
#check (Ideal.Fiber.localizationEquivTensor_algebraMap_tmul p qbar :
  ∀ (k : p.ResidueField) (s : S),
    Ideal.Fiber.localizationEquivTensor p qbar
      (algebraMap (p.Fiber S) (Localization.AtPrime qbar) (k ⊗ₜ[R] s)) =
        algebraMap S (Localization.AtPrime
          (qbar.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S))) s
            ⊗ₜ[Localization.AtPrime p] k)

/- Primes q of S lying over p correspond uniquely to primes qbar
of p.Fiber S. The inverse correspondence contracts qbar along
Algebra.TensorProduct.includeRight to recover q. -/
#check (PrimeSpectrum.primesOverOrderIsoFiber R S p :
  p.primesOver S ≃o PrimeSpectrum (p.Fiber S))

end
