module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.ProjectiveCriterion
import StacksCheckRecall

/-!
# Projectivity and Ext for two-term complexes

Lemma 15.85.1 identifies projectivity of the degree-zero cohomology of a two-term derived
module with degree-one Ext vanishing, including the finite-test Noetherian form.

@stack 0G9C
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedExt

universe u

/- Lemma 15.85.1 (0G9C), unrestricted module criterion. -/
@[stacks 0G9C "Lemma 15.85.1 (1)-(2)"]
#check fun {R : Type u} [Ring R] (K : DerivedCategory (ModuleCat R))
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0) =>
  (CategoryTheory.DerivedCategory.TwoTerm.cohomology_projective_iff_extOne_vanishes
      K hKGE hKLE :
    (IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj K) ∧
        Projective ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj K)) ↔
      ∀ (M : ModuleCat R), ∀ e : Ext⁽(1 : ℤ)⁾(K,
        (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M), e = 0)

/- Lemma 15.85.1 (0G9C), finite-module criterion over a Noetherian ring. -/
@[stacks 0G9C "Lemma 15.85.1, Noetherian case"]
#check fun {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat R)) (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hHneg1 : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj K))
    (hH0 : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj K)) =>
  (CategoryTheory.DerivedCategory.TwoTerm.cohomology_projective_extOne_tfae_of_noetherian
      K hKGE hKLE hHneg1 hH0 :
    List.TFAE [
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj K) ∧
        Projective ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj K),
      ∀ (M : ModuleCat R), ∀ e : Ext⁽(1 : ℤ)⁾(K,
        (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M), e = 0,
      ∀ (M : ModuleCat R), Module.Finite R M → ∀ e : Ext⁽(1 : ℤ)⁾(K,
        (DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M), e = 0])

@[stacks 0G9C "degree-one Ext functor companion"]
#check fun {R : Type u} [Ring R] (K : DerivedCategory (ModuleCat R))
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0) =>
  (CategoryTheory.DerivedCategory.TwoTerm.cohomology_projective_iff_extOneFunctor_isZero
      K hKGE hKLE :
    (IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj K) ∧
        Projective ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj K)) ↔
      IsZero (CategoryTheory.DerivedCategory.Ext.addCommGrpFunctor K (1 : ℤ)))
