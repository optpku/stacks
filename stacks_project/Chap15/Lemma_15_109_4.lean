/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.AdicCompletion.Algebraization

/-!
@stack 0ALR
-/

@[expose] public section

universe u v w x

/- Lemma 15.109.4: let `A` be Noetherian, `I` an ideal, and `B` a finite type
`A`-algebra.  A surjective `A`-algebra map from the `I`-adic completion of `B`
whose kernel cotangent module is annihilated by a power of `I` has a finite
type algebra model.  This historical snapshot is the current Stacks Lemma
15.110.4, tag `0ALR`. -/
@[stacks 0ALR "Lemma 15.109.4"]
#check fun (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    [CommRing C] [Algebra A C]
    (I : Ideal A)
    (φ : AdicCompletion (Ideal.map (algebraMap A B) I) B →ₐ[A] C)
    (hφ : Function.Surjective φ) (c : ℕ)
    (hker :
      Ideal.map
          (algebraMap A (AdicCompletion (Ideal.map (algebraMap A B) I) B)) (I ^ c) ≤
        Module.annihilator
          (AdicCompletion (Ideal.map (algebraMap A B) I) B)
          (RingHom.ker φ).Cotangent) ↦
  (AdicCompletion.Algebraization.exists_finiteTypeAlgEquiv_of_kernelCotangent_annihilated
      I φ hφ c hker :
    ∃ (D : Type x) (_ : CommRing D) (_ : Algebra A D)
      (_ : Algebra.FiniteType A D),
      Nonempty
        (AdicCompletion (Ideal.map (algebraMap A D) I) D ≃ₐ[A] C))

end
