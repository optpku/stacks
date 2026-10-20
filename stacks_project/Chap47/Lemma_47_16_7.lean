module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.CohenMacaulay
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped ENat

universe u

/- Lemma 47.16.7 (1): For a finite module over a Noetherian local ring, being zero or
Cohen-Macaulay is equivalent to derived Ext into a normalized dualizing complex being
nonzero in at most one degree. -/
@[stacks 0B5A] #check
  (@CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.cohenMacaulay_iff_ext_nonzeroAtMostOne :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)
      (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M],
      (Subsingleton M ∨ Module.CohenMacaulay A M) ↔
        ∀ i j : ℤ,
          ¬ IsZero
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
                ((MonoidalClosed.ihomOf H (ModuleCat.single0 (ModuleCat.of A M))).obj ω)) →
            ¬ IsZero
                ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
                  ((MonoidalClosed.ihomOf H (ModuleCat.single0 (ModuleCat.of A M))).obj ω)) →
              i = j)

/- Lemma 47.16.7 (2): For a finite module over a Noetherian local ring, being zero or
Cohen-Macaulay is equivalent to derived Ext vanishing in every degree in the zero-support
case, or away from the negative support dimension otherwise. -/
@[stacks 0B5A] #check
  (@CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.cohenMacaulay_iff_ext_isZero_off_supportDim :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)
      (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M],
      (Subsingleton M ∨ Module.CohenMacaulay A M) ↔
        (Module.supportDim A M = ⊥ ∧
          ∀ i : ℤ,
            IsZero
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-i)).obj
                ((MonoidalClosed.ihomOf H (ModuleCat.single0 (ModuleCat.of A M))).obj ω))) ∨
        ∃ d : ℕ, Module.supportDim A M = .some (d : ℕ∞) ∧
          ∀ i : ℤ, i ≠ (d : ℤ) →
            IsZero
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-i)).obj
                ((MonoidalClosed.ihomOf H (ModuleCat.single0 (ModuleCat.of A M))).obj ω)))

/- Lemma 47.16.7 (3): Degree-`-d` Ext into a normalized dualizing complex is an
anti-auto-equivalence of finite Cohen-Macaulay modules of depth `d`. -/
@[stacks 0B5A] #check
  (@CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.cohenMacaulayDualityIsEquivalence :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)
      (d : ℕ),
      (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.cohenMacaulayDuality
        H ω hω d).IsEquivalence)
