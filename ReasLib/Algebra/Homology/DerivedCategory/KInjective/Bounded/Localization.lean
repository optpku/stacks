/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.FullyFaithful.Target

@[expose] public section

/-!
# Bounded-Below K-Injectives and Localization

This leaf packages the full-faithfulness of a quasi-isomorphism localization on morphisms into a
bounded-below K-injective object.  It is independent of the chosen localization model and supplies
the neutral computation API used by pointwise derived functors.
-/

open CategoryTheory ComplexShape

universe v v' u u'

namespace HomotopyCategory.Plus.KInjective

variable {A : Type u} [Category.{v} A] [Abelian A]
  {D : Type u'} [Category.{v'} D]

/-- A bounded-below K-injective target makes the morphism map of every quasi-isomorphism
localization bijective. -/
@[stacks 05TH "bounded-below K-injective localization map is bijective"]
theorem map_bijective
    (L : HomotopyCategory.Plus A ⥤ D)
    [L.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    (K I : HomotopyCategory.Plus A) [CochainComplex.IsKInjective I.obj.as] :
    Function.Bijective (L.map : (K ⟶ I) → (L.obj K ⟶ L.obj I)) := sorry

/-- Stacks 05TH: a bounded-below K-injective target computes morphisms in any localization of
`HomotopyCategory.Plus A` at quasi-isomorphisms. -/
@[stacks 05TH "bounded-below K-injective localization"]
noncomputable def homEquiv
    (L : HomotopyCategory.Plus A ⥤ D)
    [L.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    (K I : HomotopyCategory.Plus A) [CochainComplex.IsKInjective I.obj.as] :
    (K ⟶ I) ≃ (L.obj K ⟶ L.obj I) :=
  Equiv.ofBijective L.map (map_bijective L K I)

/-- Applying `homEquiv` is the morphism map of the chosen localization. -/
@[simp, stacks 05TH "bounded-below K-injective localization map"]
theorem homEquiv_apply
    (L : HomotopyCategory.Plus A ⥤ D)
    [L.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    (K I : HomotopyCategory.Plus A) [CochainComplex.IsKInjective I.obj.as]
    (f : K ⟶ I) :
    homEquiv L K I f = L.map f := sorry

/-- The bounded-below K-injective localization equivalence is contravariantly natural in its
source. -/
theorem homEquiv_naturality_left
    (L : HomotopyCategory.Plus A ⥤ D)
    [L.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    {K K' : HomotopyCategory.Plus A} (I : HomotopyCategory.Plus A)
    [CochainComplex.IsKInjective I.obj.as]
    (f : K' ⟶ K) (g : K ⟶ I) :
    homEquiv L K' I (f ≫ g) = L.map f ≫ homEquiv L K I g := sorry

/-- The bounded-below K-injective localization equivalence is covariantly natural along maps
between K-injective targets. -/
theorem homEquiv_naturality_right
    (L : HomotopyCategory.Plus A ⥤ D)
    [L.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    (K : HomotopyCategory.Plus A) (I J : HomotopyCategory.Plus A)
    [CochainComplex.IsKInjective I.obj.as] [CochainComplex.IsKInjective J.obj.as]
    (f : K ⟶ I) (g : I ⟶ J) :
    homEquiv L K J (f ≫ g) = homEquiv L K I f ≫ L.map g := sorry

/-- Mapping the inverse bounded K-injective equivalence recovers the localized morphism. -/
@[simp]
theorem homEquiv_map_symm_apply
    (L : HomotopyCategory.Plus A ⥤ D)
    [L.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    (K I : HomotopyCategory.Plus A) [CochainComplex.IsKInjective I.obj.as]
    (f : L.obj K ⟶ L.obj I) :
    L.map ((homEquiv L K I).symm f) = f := sorry

/-- Applying the inverse bounded K-injective equivalence to a mapped morphism recovers that
morphism. -/
@[simp]
theorem homEquiv_symm_map
    (L : HomotopyCategory.Plus A ⥤ D)
    [L.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    (K I : HomotopyCategory.Plus A) [CochainComplex.IsKInjective I.obj.as]
    (f : K ⟶ I) :
    (homEquiv L K I).symm (L.map f) = f := sorry

/-- Any bounded-below quasi-isomorphism localization is fully faithful on all morphisms into a
K-injective target. -/
@[stacks 05TH "bounded-below K-injective targetwise full faithfulness"]
noncomputable def fullyFaithfulTo
    (L : HomotopyCategory.Plus A ⥤ D)
    [L.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
    (I : HomotopyCategory.Plus A) [CochainComplex.IsKInjective I.obj.as] :
    L.FullyFaithfulTo I where
  preimage f := (homEquiv L _ I).symm f
  map_preimage f := homEquiv_map_symm_apply L _ I f
  preimage_map f := homEquiv_symm_map L _ I f



end HomotopyCategory.Plus.KInjective
