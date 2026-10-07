module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Locus
public import stacks_project.Chap93.Lemma_93_13_2_Localization

/-!
# Localizing first-order extensions of a finite type algebra over a field

If `k → B` is of finite type and `S ⊆ B` meets no prime at which
`Spec B → Spec k` fails to be smooth, localization induces a bijection on
first-order square-zero extensions `Exal_k(B, N)`.
-/

@[expose] public section

noncomputable section

universe u

open Algebra
open PrimeSpectrum

namespace Algebra.Exal

variable (k B N : Type u) [Field k] [CommRing B] [Algebra k B]
variable [AddCommGroup N] [Module B N]

/-- Lemma 93.13.2
Let `k` be a field. Let `B` be a finite type `k`-algebra. Let `S ⊆ B` be a
multiplicative subset such that if `Spec B → Spec k` is not smooth at `q`
then `S ∩ q = ∅`. Let `N` be a finite `B`-module. Then localization induces a
canonical bijection `Exal k B N → Exal k (Localization S) (LocalizedModule S N)`.
-/
@[stacks 0DZ8]
theorem localize_bijective [Algebra.FiniteType k B] [Module.Finite B N]
    (S : Submonoid B)
    (hS : ∀ q : PrimeSpectrum B, q ∉ smoothLocus k B →
      (S : Set B) ∩ q.asIdeal = ∅) :
    Function.Bijective (localize k B N S) := sorry

end Algebra.Exal
