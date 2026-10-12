/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.Ext

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ENat

universe u

/- Lemma 47.16.5 (1) -/
@[stacks 0A7U] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.extDegreeBounds :
    ∀ (A M : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [AddCommGroup M] [Module A M] [Module.Finite A M]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)
      (i : ℤ),
      ¬ IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((MonoidalClosed.ihomOf H (ModuleCat.single0 (ModuleCat.of A M))).obj ω)) →
      ∃ d : ℕ, Module.supportDim A M = .some (d : ℕ∞) ∧ -(d : ℤ) ≤ i ∧ i ≤ 0)

/- Lemma 47.16.5 (2) -/
@[stacks 0A7U] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.supportDim_ext_le :
    ∀ (A M : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [AddCommGroup M] [Module A M] [Module.Finite A M]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)
      (i : ℤ),
      Module.supportDim A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((MonoidalClosed.ihomOf H (ModuleCat.single0 (ModuleCat.of A M))).obj ω)) = ⊥ ∨
        ∃ e : ℕ, Module.supportDim A
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
              ((MonoidalClosed.ihomOf H (ModuleCat.single0 (ModuleCat.of A M))).obj ω)) =
          .some (e : ℕ∞) ∧ (e : ℤ) ≤ -i)

/- Lemma 47.16.5 (3) -/
@[stacks 0A7U] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.depth_eq_sInf_nonzero_extDegrees :
    ∀ (A M : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [AddCommGroup M] [Module A M] [Module.Finite A M]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H),
      moduleDepth A M =
        sInf {d : ℕ∞ | ∃ δ : ℕ, d = (δ : ℕ∞) ∧
          ¬ IsZero
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(δ : ℤ))).obj
              ((MonoidalClosed.ihomOf H (ModuleCat.single0 (ModuleCat.of A M))).obj ω))})
