/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Algebraization of quotients of adic completions

@stack 0ALR

The algebraization criterion is owned here at the ring-map level.  The
`AlgHom` refinement below keeps the base-algebra structure needed by chapter
applications, while the ring-map theorem is reusable without an auxiliary
algebra structure on the target.
-/

universe u v w x

namespace AdicCompletion.Algebraization

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsNoetherianRing A]
variable [CommRing B] [Algebra A B] [Algebra.FiniteType A B]

/- The ring-map form is the canonical owner: the target need not be presented
as an `A`-algebra, and the conormal module is taken over the completed source. -/
/-- Lemma 15.109.4 (tag `0ALR`): a
surjective map from the completion of a finite type algebra algebraizes when a
power of the base ideal annihilates the kernel cotangent module. -/
@[stacks 0ALR "adic-completion algebraization criterion"]
theorem exists_finiteType_of_kernelCotangent_annihilated
    {C : Type w} [CommRing C]
    (I : Ideal A)
    (φ : AdicCompletion (Ideal.map (algebraMap A B) I) B →+* C)
    (hφ : Function.Surjective φ) (c : ℕ)
    (hker :
      Ideal.map
          (algebraMap A (AdicCompletion (Ideal.map (algebraMap A B) I) B)) (I ^ c) ≤
        Module.annihilator
          (AdicCompletion (Ideal.map (algebraMap A B) I) B)
          (RingHom.ker φ).Cotangent) :
    ∃ (D : Type x) (_ : CommRing D) (_ : Algebra A D)
      (_ : Algebra.FiniteType A D),
      Nonempty
        (AdicCompletion (Ideal.map (algebraMap A D) I) D ≃+* C) := sorry
-- Proof strategy: apply the Noetherian adic algebraization theorem to the finite-type
-- presentation of `B`; the annihilator bound kills the kernel cotangent obstruction and
-- yields a finite-type model whose completion is ring-equivalent to `C`.

/- The algebra form is a separate companion rather than the root owner: it
retains scalar compatibility in the output and is the convenient chapter view. -/
/-- The algebra-valued form of the adic-completion algebraization criterion.
It preserves the `A`-algebra structure of a surjective completion map and
returns an `A`-algebra equivalence. -/
@[stacks 0ALR "adic-completion algebraization as an algebra equivalence"]
theorem exists_finiteTypeAlgEquiv_of_kernelCotangent_annihilated
    {C : Type w} [CommRing C] [Algebra A C]
    (I : Ideal A)
    (φ : AdicCompletion (Ideal.map (algebraMap A B) I) B →ₐ[A] C)
    (hφ : Function.Surjective φ) (c : ℕ)
    (hker :
      Ideal.map
          (algebraMap A (AdicCompletion (Ideal.map (algebraMap A B) I) B)) (I ^ c) ≤
        Module.annihilator
          (AdicCompletion (Ideal.map (algebraMap A B) I) B)
          (RingHom.ker φ.toRingHom).Cotangent) :
    ∃ (D : Type x) (_ : CommRing D) (_ : Algebra A D)
      (_ : Algebra.FiniteType A D),
      Nonempty
        (AdicCompletion (Ideal.map (algebraMap A D) I) D ≃ₐ[A] C) := sorry
-- Proof strategy: apply the ring-map algebraization theorem to `φ.toRingHom`, then use the
-- scalar compatibility of `φ` and the canonical completion algebra structures to upgrade the
-- resulting ring equivalence to an `A`-algebra equivalence.

end AdicCompletion.Algebraization
