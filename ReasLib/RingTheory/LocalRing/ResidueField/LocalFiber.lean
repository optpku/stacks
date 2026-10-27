/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

@[expose] public section

open scoped TensorProduct
open Algebra.TensorProduct

noncomputable section
universe u v

namespace Ideal.Fiber

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

-- Local instance justification (defeq pin): Pin the tensor factor to Localization.localRingHom; priority 100 preserves the existing R_p-algebra on the localized fiber.
attribute [local instance 100] Localization.AtPrime.algebraOfLiesOver

/-- The tensor product of `S_q` with `κ(p)` over `R_p` is the quotient by
`p S_q`. The maps are Mathlib's actual tensor/quotient comparison maps. -/
noncomputable def tensorResidueEquivQuotient (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] :
    (Localization.AtPrime q ⊗[Localization.AtPrime p] p.ResidueField) ≃ₐ[Localization.AtPrime p]
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) :=
  ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot
    (Localization.AtPrime q) (IsLocalRing.maximalIdeal (Localization.AtPrime p))).symm.restrictScalars
      (Localization.AtPrime p)).trans <|
        Ideal.quotientEquivAlgOfEq (Localization.AtPrime p) (by
          rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
            ← IsScalarTower.algebraMap_eq])

/-- The localization of the fiber `p.Fiber S` at a prime `qbar` is isomorphic over
`Localization.AtPrime p` to the tensor product of the localization of `S` at the
contraction of `qbar` along `includeRight` with `p.ResidueField`. -/
noncomputable def localizationEquivTensor (p : Ideal R) [p.IsPrime]
    (qbar : Ideal (p.Fiber S)) [qbar.IsPrime] :
    Localization.AtPrime qbar ≃ₐ[Localization.AtPrime p]
      (Localization.AtPrime (qbar.comap (includeRight : S →ₐ[R] p.Fiber S))
        ⊗[Localization.AtPrime p] p.ResidueField) :=
  (Ideal.Fiber.localizationAlgEquivQuotient p qbar).trans
    (tensorResidueEquivQuotient p (qbar.comap (includeRight : S →ₐ[R] p.Fiber S))).symm

/-- The comparison identifies the localization map with the obvious map on
elementary tensors; this records its canonical orientation. -/
theorem localizationEquivTensor_algebraMap_tmul (p : Ideal R) [p.IsPrime]
    (qbar : Ideal (p.Fiber S)) [qbar.IsPrime] (k : p.ResidueField) (s : S) :
    localizationEquivTensor p qbar
      (algebraMap (p.Fiber S) (Localization.AtPrime qbar) (k ⊗ₜ[R] s)) =
        algebraMap S (Localization.AtPrime
          (qbar.comap (includeRight : S →ₐ[R] p.Fiber S))) s ⊗ₜ[Localization.AtPrime p] k := sorry

end Ideal.Fiber
