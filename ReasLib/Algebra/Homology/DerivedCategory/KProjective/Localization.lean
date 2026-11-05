/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.KProjective
public import ReasLib.Algebra.Homology.HomotopyCategory.KProjective.Characterization
public import ReasLib.CategoryTheory.Functor.FullyFaithful.Source
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# K-Projective Complexes and Derived Localization

This leaf characterizes K-projectivity by the homotopy-to-derived comparison
map. It is the projective dual of
`Algebra.Homology.DerivedCategory.KInjective.Localization`.
-/

open CategoryTheory
open ComplexShape

universe w v' v u' u

namespace CochainComplex.IsKProjective

variable {A : Type u} [Category.{v} A] [Abelian A]

section HomEquiv

variable {D : Type u'} [Category.{v'} D]

/-- For a K-projective source, every quasi-isomorphism localization is bijective on morphisms
out of its homotopy-category image. -/
@[stacks 064B "K-projective localization map is bijective"]
theorem map_bijective
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (P : CochainComplex A ℤ) (K : HomotopyCategory A (up ℤ)) [P.IsKProjective] :
    Function.Bijective
      (L.map :
        ((HomotopyCategory.quotient A (up ℤ)).obj P ⟶ K) →
          (L.obj ((HomotopyCategory.quotient A (up ℤ)).obj P) ⟶ L.obj K)) := by
  letI : L.IsLocalization (HomotopyCategory.subcategoryAcyclic A).trW := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  exact (CochainComplex.IsKProjective.leftOrthogonal P).map_bijective_of_isTriangulated L K

/-- Stacks 064B, generalized from bounded-above termwise-projective complexes: a K-projective
source computes morphisms in any localization of the homotopy category at quasi-isomorphisms. -/
@[stacks 064B "K-projective localization generalization"]
noncomputable def homEquiv
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (P : CochainComplex A ℤ) (K : HomotopyCategory A (up ℤ)) [P.IsKProjective] :
    ((HomotopyCategory.quotient A (up ℤ)).obj P ⟶ K) ≃
      (L.obj ((HomotopyCategory.quotient A (up ℤ)).obj P) ⟶ L.obj K) :=
  Equiv.ofBijective L.map (map_bijective L P K)

/-- Applying `homEquiv` is the map on morphisms induced by the chosen localization functor. -/
@[simp]
theorem homEquiv_apply
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (P : CochainComplex A ℤ) (K : HomotopyCategory A (up ℤ)) [P.IsKProjective]
    (f : (HomotopyCategory.quotient A (up ℤ)).obj P ⟶ K) :
    homEquiv L P K f = L.map f := rfl

/-- The K-projective localization equivalence is contravariantly natural along homotopy
morphisms between K-projective sources. -/
theorem homEquiv_naturality_left
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (P Q : CochainComplex A ℤ) (K : HomotopyCategory A (up ℤ))
    [P.IsKProjective] [Q.IsKProjective]
    (f : (HomotopyCategory.quotient A (up ℤ)).obj P ⟶
      (HomotopyCategory.quotient A (up ℤ)).obj Q)
    (g : (HomotopyCategory.quotient A (up ℤ)).obj Q ⟶ K) :
    homEquiv L P K (f ≫ g) = L.map f ≫ homEquiv L Q K g := by
  exact L.map_comp f g

/-- The K-projective localization equivalence is covariantly natural in its homotopy-category
target. -/
theorem homEquiv_naturality_right
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (P : CochainComplex A ℤ) {K K' : HomotopyCategory A (up ℤ)} [P.IsKProjective]
    (f : (HomotopyCategory.quotient A (up ℤ)).obj P ⟶ K) (g : K ⟶ K') :
    homEquiv L P K' (f ≫ g) = homEquiv L P K f ≫ L.map g := by
  exact L.map_comp f g

/-- Mapping the inverse of the K-projective localization equivalence recovers the localized
morphism. -/
@[simp]
theorem homEquiv_map_symm_apply
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (P : CochainComplex A ℤ) (K : HomotopyCategory A (up ℤ)) [P.IsKProjective]
    (f : L.obj ((HomotopyCategory.quotient A (up ℤ)).obj P) ⟶ L.obj K) :
    L.map ((homEquiv L P K).symm f) = f := by
  exact (homEquiv L P K).apply_symm_apply f

/-- Applying the inverse K-projective localization equivalence to a mapped homotopy morphism
recovers that morphism. -/
@[simp]
theorem homEquiv_symm_map
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (P : CochainComplex A ℤ) (K : HomotopyCategory A (up ℤ)) [P.IsKProjective]
    (f : (HomotopyCategory.quotient A (up ℤ)).obj P ⟶ K) :
    (homEquiv L P K).symm (L.map f) = f := by
  exact (homEquiv L P K).symm_apply_apply f

/-- Any quasi-isomorphism localization is fully faithful on all morphisms from the image of a
K-projective complex. -/
@[stacks 064B "K-projective sourcewise full faithfulness"]
noncomputable def fullyFaithfulFrom
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (P : CochainComplex A ℤ) [P.IsKProjective] :
    L.FullyFaithfulFrom ((HomotopyCategory.quotient A (up ℤ)).obj P) where
  preimage f := (homEquiv L P _).symm f
  map_preimage f := homEquiv_map_symm_apply L P _ f
  preimage_map f := homEquiv_symm_map L P _ f

namespace Replacement

/-- Stacks 064B, projective-replacement form: a quasi-isomorphism from a K-projective source to
`M` computes localized morphisms out of `M`. -/
@[stacks 064B "K-projective replacement"]
noncomputable def homEquiv
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (P : CochainComplex A ℤ) (M K : HomotopyCategory A (up ℤ)) [P.IsKProjective]
    (p : (HomotopyCategory.quotient A (up ℤ)).obj P ⟶ M)
    (hp : HomotopyCategory.quasiIso A (up ℤ) p) :
    ((HomotopyCategory.quotient A (up ℤ)).obj P ⟶ K) ≃ (L.obj M ⟶ L.obj K) :=
  (IsKProjective.homEquiv L P K).trans
    (Iso.homCongr
      (CategoryTheory.Localization.isoOfHom L
        (HomotopyCategory.quasiIso A (up ℤ)) p hp)
      (Iso.refl _))

/-- Applying `Replacement.homEquiv` localizes the homotopy morphism after precomposing with
the inverse of the localized replacement quasi-isomorphism. -/
@[simp]
theorem homEquiv_apply
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (P : CochainComplex A ℤ) (M K : HomotopyCategory A (up ℤ)) [P.IsKProjective]
    (p : (HomotopyCategory.quotient A (up ℤ)).obj P ⟶ M)
    (hp : HomotopyCategory.quasiIso A (up ℤ) p)
    (f : (HomotopyCategory.quotient A (up ℤ)).obj P ⟶ K) :
    homEquiv L P M K p hp f =
      (CategoryTheory.Localization.isoOfHom L
        (HomotopyCategory.quasiIso A (up ℤ)) p hp).inv ≫ L.map f := sorry

/-- Mapping the inverse image of a localized morphism through a K-projective replacement
recovers the localized replacement quasi-isomorphism followed by that morphism. -/
@[stacks 064B, simp]
theorem homEquiv_map_symm_apply
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (P : CochainComplex A ℤ) (M K : HomotopyCategory A (up ℤ)) [P.IsKProjective]
    (p : (HomotopyCategory.quotient A (up ℤ)).obj P ⟶ M)
    (hp : HomotopyCategory.quasiIso A (up ℤ) p)
    (f : L.obj M ⟶ L.obj K) :
    L.map ((homEquiv L P M K p hp).symm f) = L.map p ≫ f := sorry

/-- The projective-replacement computation equivalence is covariantly natural in its
homotopy-category target. -/
theorem homEquiv_naturality_right
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (P : CochainComplex A ℤ) (M : HomotopyCategory A (up ℤ))
    {K K' : HomotopyCategory A (up ℤ)} [P.IsKProjective]
    (p : (HomotopyCategory.quotient A (up ℤ)).obj P ⟶ M)
    (hp : HomotopyCategory.quasiIso A (up ℤ) p)
    (f : (HomotopyCategory.quotient A (up ℤ)).obj P ⟶ K) (g : K ⟶ K') :
    homEquiv L P M K' p hp (f ≫ g) = homEquiv L P M K p hp f ≫ L.map g := sorry

/-- The K-projective replacement equivalence is natural under a commutative square between two
replacement quasi-isomorphisms. -/
theorem homEquiv_naturality_replacement
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (P Q : CochainComplex A ℤ) (M N K : HomotopyCategory A (up ℤ))
    [P.IsKProjective] [Q.IsKProjective]
    (p : (HomotopyCategory.quotient A (up ℤ)).obj P ⟶ M)
    (hp : HomotopyCategory.quasiIso A (up ℤ) p)
    (q : (HomotopyCategory.quotient A (up ℤ)).obj Q ⟶ N)
    (hq : HomotopyCategory.quasiIso A (up ℤ) q)
    (a : M ⟶ N)
    (b : (HomotopyCategory.quotient A (up ℤ)).obj P ⟶
      (HomotopyCategory.quotient A (up ℤ)).obj Q)
    (sq : CommSq p b a q)
    (f : (HomotopyCategory.quotient A (up ℤ)).obj Q ⟶ K) :
    homEquiv L P M K p hp (b ≫ f) = L.map a ≫ homEquiv L Q N K q hq f := sorry

end Replacement

end HomEquiv

/-- A cochain complex is K-projective exactly when any quasi-isomorphism localization is
sourcewise bijective on all morphisms out of its homotopy-category image. -/
@[stacks 064B "K-projective localization characterization"]
theorem iff_map_bijective {D : Type u'} [Category.{v'} D]
    (L : HomotopyCategory A (up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (up ℤ))]
    (P : CochainComplex A ℤ) :
    P.IsKProjective ↔
      ∀ K : HomotopyCategory A (up ℤ),
        Function.Bijective
          (L.map : ((HomotopyCategory.quotient A (up ℤ)).obj P ⟶ K) →
            (L.obj ((HomotopyCategory.quotient A (up ℤ)).obj P) ⟶ L.obj K)) := sorry

/-- Stacks 064B, generalized from bounded-above termwise-projective complexes: a cochain
complex is K-projective exactly when the canonical homotopy-to-derived map out of it is
bijective for every homotopy-category target. -/
@[stacks 064B "K-projective localization characterization"]
theorem iff_Qh_map_bijective [HasDerivedCategory.{w} A]
    (P : CochainComplex A ℤ) :
    P.IsKProjective ↔
      ∀ K : HomotopyCategory A (up ℤ),
        Function.Bijective
          (DerivedCategory.Qh.map :
            ((HomotopyCategory.quotient A (up ℤ)).obj P ⟶ K) →
              (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (up ℤ)).obj P) ⟶
                DerivedCategory.Qh.obj K)) := sorry

end CochainComplex.IsKProjective
