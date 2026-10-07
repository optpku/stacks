module

public import ReasLib.RingTheory.CohenMacaulay.Module.Subcategory
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.Ext
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Duality

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open scoped ENat

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
variable (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)

include hω

/-- Derived duality in degree `-d` carries a Cohen-Macaulay module of depth `d` to
another Cohen-Macaulay module of depth `d`. -/
theorem cohenMacaulayDualityObjMem (d : ℕ)
    (M : ((ModuleCat.cohenMacaulayOfDepth A d).FullSubcategory)ᵒᵖ) :
    ModuleCat.cohenMacaulayOfDepth A d
      (((((ModuleCat.cohenMacaulayOfDepth A d).ι ⋙ ModuleCat.single0Functor).op ⋙
          MonoidalClosed.sourceFunctorOf H ω) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj M) := sorry

/-- Degree-`-d` Ext into `ω`, restricted to Cohen-Macaulay modules of depth `d`. -/
noncomputable def cohenMacaulayDuality (d : ℕ) :
    ((ModuleCat.cohenMacaulayOfDepth A d).FullSubcategory)ᵒᵖ ⥤
      (ModuleCat.cohenMacaulayOfDepth A d).FullSubcategory :=
  (ModuleCat.cohenMacaulayOfDepth A d).lift
    ((((ModuleCat.cohenMacaulayOfDepth A d).ι ⋙ ModuleCat.single0Functor).op ⋙
        MonoidalClosed.sourceFunctorOf H ω) ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ)))
    (cohenMacaulayDualityObjMem H ω hω d)

/-- The underlying module of `cohenMacaulayDuality H ω hω d` is degree-`-d`
cohomology of derived internal Hom into `ω`. -/
theorem cohenMacaulayDuality_obj (d : ℕ)
    (M : ((ModuleCat.cohenMacaulayOfDepth A d).FullSubcategory)ᵒᵖ) :
    ((cohenMacaulayDuality H ω hω d).obj M).obj =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj
        ((MonoidalClosed.ihomOf H (ModuleCat.single0 M.unop.obj)).obj ω) := sorry

/-- For a finite module over a Noetherian local ring, being zero or Cohen-Macaulay is
equivalent to derived Ext into a normalized dualizing complex being nonzero in at most one
degree. -/
theorem cohenMacaulay_iff_ext_nonzeroAtMostOne
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    (Subsingleton M ∨ Module.CohenMacaulay A M) ↔
      ∀ i j : ℤ,
        ¬ IsZero
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
              ((MonoidalClosed.ihomOf H (ModuleCat.single0 (ModuleCat.of A M))).obj ω)) →
          ¬ IsZero
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
                ((MonoidalClosed.ihomOf H (ModuleCat.single0 (ModuleCat.of A M))).obj ω)) →
            i = j := sorry

/-- For a finite module over a Noetherian local ring, being zero or Cohen-Macaulay is
equivalent to derived Ext vanishing in every degree in the zero-support case, or away from
the negative support dimension otherwise. -/
theorem cohenMacaulay_iff_ext_isZero_off_supportDim
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] :
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
              ((MonoidalClosed.ihomOf H (ModuleCat.single0 (ModuleCat.of A M))).obj ω)) := sorry

/-- Degree-`-d` Ext into a normalized dualizing complex is an anti-equivalence on finite
Cohen-Macaulay modules of depth `d`. -/
theorem cohenMacaulayDualityIsEquivalence (d : ℕ) :
    (cohenMacaulayDuality H ω hω d).IsEquivalence := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
