/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.KInjective
public import ReasLib.Algebra.Homology.HomotopyCategory.KInjective.Local
public import ReasLib.CategoryTheory.Functor.FullyFaithful.Target
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# K-Injective Complexes and Derived Localization

This leaf characterizes K-injectivity by the homotopy-to-derived comparison
map. It is the derived-category counterpart of the homotopy-local criterion
in `HomotopyCategory.KInjective.Local`.
-/

open CategoryTheory
open ComplexShape

universe w v' v u' u

namespace CochainComplex.IsKInjective

variable {A : Type u} [Category.{v} A] [Abelian A]

section HomEquiv

variable {D : Type u'} [Category.{v'} D]

/-- For a K-injective target, every quasi-isomorphism localization is bijective on morphisms
into its homotopy-category image. -/
@[stacks 070I "K-injective localization map is bijective"]
theorem map_bijective
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (K : HomotopyCategory A (up ℤ)) (I : CochainComplex A ℤ) [I.IsKInjective] :
    Function.Bijective
      (L.map :
        (K ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I) →
          (L.obj K ⟶ L.obj ((HomotopyCategory.quotient A (up ℤ)).obj I))) := sorry

/-- A K-injective target computes morphisms in any localization of the homotopy category at
quasi-isomorphisms. The source is a Hom type in `HomotopyCategory A (up ℤ)`, and the target is the
corresponding Hom type after applying the localization functor `L`. -/
@[stacks 070I]
noncomputable def homEquiv
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (K : HomotopyCategory A (up ℤ)) (I : CochainComplex A ℤ) [I.IsKInjective] :
    (K ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I) ≃
      (L.obj K ⟶ L.obj ((HomotopyCategory.quotient A (up ℤ)).obj I)) :=
  Equiv.ofBijective L.map (map_bijective L K I)

/-- Applying `homEquiv` is the map on morphisms induced by the chosen localization functor. -/
@[simp]
theorem homEquiv_apply
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (K : HomotopyCategory A (up ℤ)) (I : CochainComplex A ℤ) [I.IsKInjective]
    (f : K ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I) :
    homEquiv L K I f = L.map f := sorry

/-- The K-injective localization equivalence is contravariantly natural in its homotopy-category
source. -/
theorem homEquiv_naturality_left
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    {K K' : HomotopyCategory A (up ℤ)} (I : CochainComplex A ℤ) [I.IsKInjective]
    (f : K' ⟶ K) (g : K ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I) :
    homEquiv L K' I (f ≫ g) = L.map f ≫ homEquiv L K I g := sorry

/-- The K-injective localization equivalence is covariantly natural along homotopy morphisms
between K-injective targets. -/
theorem homEquiv_naturality_right
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (K : HomotopyCategory A (up ℤ)) (I J : CochainComplex A ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (f : K ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I)
    (g : (HomotopyCategory.quotient A (up ℤ)).obj I ⟶
      (HomotopyCategory.quotient A (up ℤ)).obj J) :
    homEquiv L K J (f ≫ g) = homEquiv L K I f ≫ L.map g := sorry

/-- Mapping the inverse of the K-injective localization equivalence recovers the localized
morphism. -/
@[simp]
theorem homEquiv_map_symm_apply
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (K : HomotopyCategory A (up ℤ)) (I : CochainComplex A ℤ) [I.IsKInjective]
    (f : L.obj K ⟶ L.obj ((HomotopyCategory.quotient A (up ℤ)).obj I)) :
    L.map ((homEquiv L K I).symm f) = f := sorry

/-- Applying the inverse K-injective localization equivalence to a mapped homotopy morphism
recovers that morphism. -/
@[simp]
theorem homEquiv_symm_map
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (K : HomotopyCategory A (up ℤ)) (I : CochainComplex A ℤ) [I.IsKInjective]
    (f : K ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I) :
    (homEquiv L K I).symm (L.map f) = f := sorry

/-- Any quasi-isomorphism localization is fully faithful on all morphisms into the image of a
K-injective complex. -/
@[stacks 070I "K-injective targetwise full faithfulness"]
noncomputable def fullyFaithfulTo
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    L.FullyFaithfulTo ((HomotopyCategory.quotient A (up ℤ)).obj I) where
  preimage f := (homEquiv L _ I).symm f
  map_preimage f := homEquiv_map_symm_apply L _ I f
  preimage_map f := homEquiv_symm_map L _ I f

namespace Replacement

/-- A quasi-isomorphism from `N` to a K-injective target computes localized morphisms into `N`.
The source consists of homotopy morphisms into the K-injective replacement, while the target
consists of morphisms into `L.obj N` in the chosen localization. -/
@[stacks 079Q]
noncomputable def homEquiv
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (K N : HomotopyCategory A (up ℤ)) (I : CochainComplex A ℤ) [I.IsKInjective]
    (i : N ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I)
    (hi : HomotopyCategory.quasiIso A (up ℤ) i) :
    (K ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I) ≃ (L.obj K ⟶ L.obj N) :=
  (IsKInjective.homEquiv L K I).trans
    (Iso.homCongr (Iso.refl _)
      (CategoryTheory.Localization.isoOfHom L
        (HomotopyCategory.quasiIso A (up ℤ)) i hi).symm)

/-- Applying `Replacement.homEquiv` localizes the homotopy morphism and then postcomposes with
the inverse of the localized replacement quasi-isomorphism. -/
@[simp]
theorem homEquiv_apply
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (K N : HomotopyCategory A (up ℤ)) (I : CochainComplex A ℤ) [I.IsKInjective]
    (i : N ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I)
    (hi : HomotopyCategory.quasiIso A (up ℤ) i)
    (f : K ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I) :
    homEquiv L K N I i hi f =
      L.map f ≫
        (CategoryTheory.Localization.isoOfHom L
          (HomotopyCategory.quasiIso A (up ℤ)) i hi).inv := sorry

/-- Mapping the inverse image of a localized morphism through a K-injective replacement
recovers that morphism followed by the localized replacement quasi-isomorphism. -/
@[stacks 079Q, simp]
theorem homEquiv_map_symm_apply
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (K N : HomotopyCategory A (up ℤ)) (I : CochainComplex A ℤ) [I.IsKInjective]
    (i : N ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I)
    (hi : HomotopyCategory.quasiIso A (up ℤ) i)
    (f : L.obj K ⟶ L.obj N) :
    L.map ((homEquiv L K N I i hi).symm f) = f ≫ L.map i := sorry

/-- The replacement computation equivalence is contravariantly natural in its homotopy-category
source. -/
theorem homEquiv_naturality_left
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    {K K' : HomotopyCategory A (up ℤ)} (N : HomotopyCategory A (up ℤ))
    (I : CochainComplex A ℤ) [I.IsKInjective]
    (i : N ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I)
    (hi : HomotopyCategory.quasiIso A (up ℤ) i)
    (f : K' ⟶ K) (g : K ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I) :
    homEquiv L K' N I i hi (f ≫ g) = L.map f ≫ homEquiv L K N I i hi g := sorry

/-- The K-injective replacement equivalence is natural under a commutative square between two
replacement quasi-isomorphisms. -/
theorem homEquiv_naturality_replacement
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (K N M : HomotopyCategory A (up ℤ)) (I J : CochainComplex A ℤ)
    [I.IsKInjective] [J.IsKInjective]
    (i : N ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I)
    (hi : HomotopyCategory.quasiIso A (up ℤ) i)
    (j : M ⟶ (HomotopyCategory.quotient A (up ℤ)).obj J)
    (hj : HomotopyCategory.quasiIso A (up ℤ) j)
    (a : N ⟶ M)
    (b : (HomotopyCategory.quotient A (up ℤ)).obj I ⟶
      (HomotopyCategory.quotient A (up ℤ)).obj J)
    (sq : CommSq i a b j)
    (f : K ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I) :
    homEquiv L K M J j hj (f ≫ b) = homEquiv L K N I i hi f ≫ L.map a := sorry

end Replacement

end HomEquiv

/-- A cochain complex is K-injective exactly when any quasi-isomorphism localization is
targetwise bijective on all morphisms into its homotopy-category image. -/
@[stacks 070I "K-injective localization characterization"]
theorem iff_map_bijective {D : Type u'} [Category.{v'} D]
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (I : CochainComplex A ℤ) :
    I.IsKInjective ↔
      ∀ K : HomotopyCategory A (up ℤ),
        Function.Bijective
          (L.map : (K ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I) →
            (L.obj K ⟶ L.obj ((HomotopyCategory.quotient A (up ℤ)).obj I))) := sorry

/-- A cochain complex is K-injective exactly when the canonical homotopy-to-derived map into it is
bijective for every homotopy-category source. -/
@[stacks 070I]
theorem iff_Qh_map_bijective [HasDerivedCategory.{w} A]
    (I : CochainComplex A ℤ) :
    I.IsKInjective ↔
      ∀ K : HomotopyCategory A (up ℤ),
        Function.Bijective
          (DerivedCategory.Qh.map :
            (K ⟶ (HomotopyCategory.quotient A (up ℤ)).obj I) →
              (DerivedCategory.Qh.obj K ⟶
                DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (up ℤ)).obj I))) := sorry



end CochainComplex.IsKInjective
