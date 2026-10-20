/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Lemma_88_21_9
public import ReasLib.Algebra.Module.IdealPower.Predicate

/-!
# Rig-surjectivity versus special-fiber faithful flatness

If `A` is Noetherian and `I`-adically complete, `B` is an `I`-adically complete
`A`-algebra, the `I`-torsion in `A` vanishes, and each truncation
`A ⧸ I ^ n →+* B ⧸ I ^ n B` is of finite type and flat, then the induced morphism
of formal spectra `Spf(B) ⟶ Spf(A)` is rig-surjective if and only if the special
fiber `A ⧸ I →+* B ⧸ IB` is faithfully flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicSpace FormalAlgebraicSpace AffineFormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective

/-- Lemma 88.21.10: Let `A` be a Noetherian ring complete with respect to an
ideal `I`. Let `B` be an `I`-adically complete `A`-algebra. Assume that the
`I`-torsion in `A` is `0`, equivalently `I.powerTorsion A 1 = ⊥`, and that
`A ⧸ I ^ n →+* B ⧸ I ^ n B` is of finite type and flat for all `n`. Then
`Spf(B) ⟶ Spf(A)`, encoded as `spfAdicCompletionMap B hA I`, is rig-surjective
if and only if `A ⧸ I →+* B ⧸ IB` is faithfully flat. -/
@[stacks 0AQY]
theorem iff_specialFiber_faithfullyFlat
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [Algebra A B]
    (I : Ideal A) [IsAdicComplete I A] [IsAdicComplete I B]
    [Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B))]
    (h_torsion : I.powerTorsion A 1 = ⊥)
    (hfinite : ∀ n : ℕ,
      (Ideal.quotientMap ((I ^ (n + 1)).map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map).FiniteType)
    (hflat : ∀ n : ℕ,
      (Ideal.quotientMap ((I ^ (n + 1)).map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map).Flat)
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    RigSurjective (spfAdicCompletionMap B hA I) ↔
      (Ideal.quotientMap (I.map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map).FaithfullyFlat :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective
