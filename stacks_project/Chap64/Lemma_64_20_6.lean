/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.AdicTrace

/-!
# Assembling traces of a Cartesian system of perfect complexes

The stages indexed by `n` have coefficients `ZMod (ℓ ^ (n + 1))`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory.IsPerfect

/- Lemma 64.20.6. Compatible perfect prime-adic endomorphisms have an assembled trace,
finite inverse-limit cohomology in finitely many degrees, and the rational trace formula. -/
@[stacks 03V4] #check (CategoryTheory.DerivedCategory.IsPerfect.existsUnique_tracePadic :
    ∀ {ℓ : ℕ} [Fact ℓ.Prime]
      (K : (n : ℕ) → DerivedCategory (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))))
      (hK : ∀ n, (K n).IsPerfect)
      (π : ∀ n, End (K n))
      (φ : ∀ n, (derivedBaseChange ℓ n).obj (K (n + 1)) ≅ K n)
      (hπ : ∀ n,
        CommSq ((derivedBaseChange ℓ n).map (π (n + 1))) (φ n).hom (φ n).hom (π n)),
    ∃! t : ℤ_[ℓ], ∀ n, PadicInt.toZModPow (n + 1) t = stageTrace K hK π n)

#check (CategoryTheory.DerivedCategory.IsPerfect.moduleFinite_homologyLimit :
    ∀ {ℓ : ℕ} [Fact ℓ.Prime]
      (K : (n : ℕ) → DerivedCategory (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))))
      (hK : ∀ n, (K n).IsPerfect)
      (φ : ∀ n, (derivedBaseChange ℓ n).obj (K (n + 1)) ≅ K n) (i : ℤ),
    Module.Finite ℤ_[ℓ] (homologyLimit K φ i))

#check (CategoryTheory.DerivedCategory.IsPerfect.finiteSupport_homologyLimit :
    ∀ {ℓ : ℕ} [Fact ℓ.Prime]
      (K : (n : ℕ) → DerivedCategory (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))))
      (hK : ∀ n, (K n).IsPerfect)
      (φ : ∀ n, (derivedBaseChange ℓ n).obj (K (n + 1)) ≅ K n),
    {i : ℤ | ¬ IsZero (homologyLimit K φ i)}.Finite)

#check (CategoryTheory.DerivedCategory.IsPerfect.trace_eq_sum_homologyLimitEnd :
    ∀ {ℓ : ℕ} [Fact ℓ.Prime]
      (K : (n : ℕ) → DerivedCategory (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))))
      (hK : ∀ n, (K n).IsPerfect)
      (π : ∀ n, End (K n))
      (φ : ∀ n, (derivedBaseChange ℓ n).obj (K (n + 1)) ≅ K n)
      (hπ : ∀ n,
        CommSq ((derivedBaseChange ℓ n).map (π (n + 1))) (φ n).hom (φ n).hom (π n))
      (t : ℤ_[ℓ])
      (ht : ∀ n, PadicInt.toZModPow (n + 1) t = stageTrace K hK π n),
    (∑ᶠ i : ℤ, (-1 : ℚ_[ℓ]) ^ i *
        LinearMap.trace ℚ_[ℓ] _ (homologyLimitEndQEll K π φ hπ i)) =
      algebraMap ℤ_[ℓ] ℚ_[ℓ] t)
