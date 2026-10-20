/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AtPrime.TensorProduct.Pi
public import ReasLib.RingTheory.Completion.Quotient

/-!
# Finite algebras over complete local rings

This leaf owns the canonical map from a finite algebra over a Noetherian
complete local ring to the product of its completed local factors.  The map
is concrete; its bijectivity is stated separately, so the public API does not
choose an inverse from deferred proof data.
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u v

namespace IsCompleteLocalRing

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
variable {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S]

/-- Stacks Lemma 10.160.2 (2), tag `0325`: the canonical `R`-algebra map from
`S` to the product of the completed local factors over the closed point of
`R`. -/
@[stacks 0325 "finite algebra product decomposition over a complete local ring"]
noncomputable def finiteProductMap :
    S →ₐ[R]
      ∀ q : (maximalIdeal R).primesOver S,
        AdicCompletion (maximalIdeal (Localization.AtPrime q.1))
          (Localization.AtPrime q.1) :=
  (AdicCompletion.AtPrime.TensorProduct.Pi.map
    (R := R) (S := S) (maximalIdeal R)).comp
    (Algebra.TensorProduct.includeRight : S →ₐ[R]
      (AdicCompletion (maximalIdeal (Localization.AtPrime (maximalIdeal R)))
        (Localization.AtPrime (maximalIdeal R))) ⊗[R] S)

/-- Tag `0325`: the closed-point product map evaluates at `q` as the canonical
map from `S` into the completion of `S_q`. -/
@[stacks 0325 "finite algebra product decomposition over a complete local ring"]
theorem finiteProductMap_apply (s : S) (q : (maximalIdeal R).primesOver S) :
    finiteProductMap (R := R) (S := S) s q =
      algebraMap S
        (AdicCompletion (maximalIdeal (Localization.AtPrime q.1))
          (Localization.AtPrime q.1)) s := sorry

/-- Stacks Lemma 10.160.2 (2), tag `0325`: for a finite algebra over a
Noetherian complete local ring, the canonical product map is bijective. -/
@[stacks 0325 "finite algebra product decomposition over a complete local ring"]
theorem finiteProductMap_bijective :
    Function.Bijective (finiteProductMap (R := R) (S := S)) := sorry

end IsCompleteLocalRing
