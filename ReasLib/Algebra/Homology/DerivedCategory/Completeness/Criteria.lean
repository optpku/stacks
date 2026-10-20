/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.LocalizationAway
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Vanishing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalent localization-away vanishing criteria

This file owns the seven mathematical conditions in Stacks Lemma 15.92.1 as small predicates and
atomic equivalences.  It deliberately does not package them as one large conjunction.  The
Milnor product map is defined from an explicit product cone, so its data does not depend on a
locally selected `HasProduct` instance.

@stack 091P
-/

@[expose] public section

noncomputable section

open CategoryTheory.Limits
open scoped DerivedExt

universe u

namespace CategoryTheory.DerivedCategory.LocalizationAway

variable {A : Type u} [CommRing A]

/-- Vanishing of every derived extension group from `A_f[0]` to `K`.  Integer degrees are used
because the second argument is an arbitrary derived object. -/
@[stacks 091P "all-degree localization-away Ext vanishing"]
def extVanishing (f : A) (K : DerivedCategory (ModuleCat A)) : Prop :=
  ∀ n : ℤ, Subsingleton (Ext⁽n⁾((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj
    (ModuleCat.of A (Localization.Away f)), K))

/-- Vanishing of `T(H^p(K)[0], f)` in every cohomological degree `p`. -/
@[stacks 091P "cohomologywise localization-away T vanishing"]
def cohomologyTVanishing
    [MonoidalCategory (DerivedCategory (ModuleCat A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (f : A) (K : DerivedCategory (ModuleCat A)) : Prop :=
  ∀ p : ℤ, IsZero
    (localizationAwayT H f
      ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat A) p).obj K)))

/-- For every cohomology module of `K`, both `Hom_A(A_f, -)` and
`Ext^1_A(A_f, -)` vanish. -/
@[stacks 091P "cohomologywise localization-away Hom and Ext-one vanishing"]
def cohomologyLowExtVanishing (f : A) (K : DerivedCategory (ModuleCat A)) : Prop :=
  ∀ p : ℤ,
    Subsingleton
        ((ModuleCat.of A (Localization.Away f)) ⟶
          (DerivedCategory.homologyFunctor (ModuleCat A) p).obj K) ∧
      Subsingleton
        (Abelian.Ext (ModuleCat.of A (Localization.Away f))
          ((DerivedCategory.homologyFunctor (ModuleCat A) p).obj K) 1)

/-- An explicitly supplied product cone for the multiplication-by-`f` tower on `K`. -/
@[stacks 091P "localization-away tower product cone"]
abbrev ProductCone (f : A) (K : DerivedCategory (ModuleCat A)) :=
  LimitCone (Discrete.functor
    (SequentialInverseSystem.family (localizationAwayTower f K)))

/-- The Milnor endomorphism on an explicitly supplied product of the multiplication-by-`f`
tower.  Its components are `(x_n) ↦ (x_n - f x_{n+1})`. -/
@[stacks 091P "localization-away Milnor product difference"]
abbrev productDifference (f : A) (K : DerivedCategory (ModuleCat A))
    (P : ProductCone f K) : P.cone.pt ⟶ P.cone.pt :=
  SequentialInverseSystem.Milnor.ProductCone.difference (localizationAwayTower f K) P

/-! A product cone is kept explicit here because this leaf is also usable in derived categories
where countable products have not yet been installed as a global instance. -/

/-- The Milnor difference is invertible for one explicitly supplied product cone. -/
@[stacks 091P "localization-away product-difference isomorphism criterion"]
def productDifferenceIsIsoAt (f : A) (K : DerivedCategory (ModuleCat A))
    (P : ProductCone f K) : Prop :=
  IsIso (productDifference f K P)

/-- The source-facing product criterion includes an explicit existence gate and is independent of
which supplied product cone is chosen. -/
@[stacks 091P "localization-away product-difference isomorphism criterion"]
def productDifferenceIsIso (f : A) (K : DerivedCategory (ModuleCat A)) : Prop :=
  Nonempty (ProductCone f K) ∧ ∀ P : ProductCone f K, productDifferenceIsIsoAt f K P

/-- The `n`-th component of `productDifference` is the current projection minus `f` times the
successor projection. -/
@[stacks 091P "localization-away Milnor product-difference component"]
theorem productDifference_comp_projection
    (f : A) (K : DerivedCategory (ModuleCat A))
    (P : ProductCone f K) (n : ℕ) :
    productDifference f K P ≫
        SequentialInverseSystem.Milnor.ProductCone.projection P n =
      SequentialInverseSystem.Milnor.ProductCone.projection P n -
        SequentialInverseSystem.Milnor.ProductCone.projection P (n + 1) ≫
          SequentialInverseSystem.transitionMap
            (localizationAwayTower f K) (Nat.le_succ n) := sorry

/-- All derived extensions from `A_f[0]` vanish exactly when every derived `A_f`-object has zero
morphism space into `K` after restriction of scalars. -/
@[stacks 091P "all-degree Ext and all-source derived-Hom criteria"]
theorem extVanishing_iff_derivedHomVanishing (f : A)
    (K : DerivedCategory (ModuleCat A)) :
    extVanishing f K ↔
      _root_.DerivedCategory.localizationAwayDerivedHomVanishingCondition f K := sorry

/-- Vanishing of `T(K, f)` is equivalent to vanishing of `T` on every cohomology module of `K`. -/
@[stacks 091P "T vanishing and cohomologywise T vanishing"]
theorem t_isZero_iff_cohomologyTVanishing
    [MonoidalCategory (DerivedCategory (ModuleCat A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (f : A) (K : DerivedCategory (ModuleCat A)) :
    IsZero (localizationAwayT H f K) ↔ cohomologyTVanishing H f K := sorry

/-- Cohomologywise `T`-vanishing is equivalent to simultaneous `Hom` and `Ext^1` vanishing on
every cohomology module. -/
@[stacks 091P "cohomologywise T and low-Ext criteria"]
theorem cohomologyTVanishing_iff_lowExtVanishing
    [MonoidalCategory (DerivedCategory (ModuleCat A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (f : A) (K : DerivedCategory (ModuleCat A)) :
    cohomologyTVanishing H f K ↔ cohomologyLowExtVanishing f K := sorry

/-- The source-facing object `T(K, f)` vanishes exactly when the canonical derived internal Hom
`RHom_A(A_f[0], K)` vanishes. -/
@[stacks 091P "T vanishing and derived internal-Hom vanishing"]
theorem t_isZero_iff_rhom_isZero
    [MonoidalCategory (DerivedCategory (ModuleCat A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (f : A) (K : DerivedCategory (ModuleCat A)) :
    IsZero (localizationAwayT H f K) ↔
      IsZero
        (InternalHom.obj H
          ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj
            (ModuleCat.of A (Localization.Away f))) K) := sorry

/-- For any explicit product cone of the multiplication tower, the general homotopy-limit
vanishing criterion specializes to `T(K, f)`. -/
@[stacks 091P "T vanishing and Milnor product-difference criterion"]
theorem t_isZero_iff_productDifference_isIso
    [MonoidalCategory (DerivedCategory (ModuleCat A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (f : A) (K : DerivedCategory (ModuleCat A))
    (P : ProductCone f K) :
    IsZero (localizationAwayT H f K) ↔ productDifferenceIsIsoAt f K P := sorry

/-- The source-facing product criterion, with independence from the selected product cone made
explicit. -/
@[stacks 091P "T vanishing and product-difference isomorphism criterion"]
theorem t_isZero_iff_productDifferenceIsIso
    [MonoidalCategory (DerivedCategory (ModuleCat A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (f : A) (K : DerivedCategory (ModuleCat A)) :
    (IsZero (localizationAwayT H f K) ∧ Nonempty (ProductCone f K)) ↔
      productDifferenceIsIso f K := sorry

end CategoryTheory.DerivedCategory.LocalizationAway
