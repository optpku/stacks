/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.EnoughNegativeObjects
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor.TopCohomology

@[expose] public section

open CategoryTheory.Limits

universe w v u

namespace CategoryTheory.DerivedCategory.Bounded

/-- In an abelian category with enough negative objects, a bounded derived object
whose cohomology vanishes above `b` admits a map from an object concentrated in
degree `b` that is epimorphic on degree-`b` cohomology, with every map from that
cohomology object to the chosen source object equal to zero. -/
theorem exists_shifted_map_with_surjective_top_cohomology
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (hneg : HasEnoughNegativeObjects C) (X : DerivedCategory.Bounded C) (b : ℤ)
    (hvanish : ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.Bounded.homologyFunctor C i).obj X)) :
    ∃ (N : C)
      (f : (DerivedCategory.Bounded.singleFunctor C b).obj N ⟶ X),
      Epi (topCohomologyMap b X f) ∧
        ∀ g : (DerivedCategory.Bounded.homologyFunctor C b).obj X ⟶ N, g = 0 := sorry

/-- In an abelian category with enough negative objects, a morphism between
bounded derived objects with the relevant upper cohomology vanishings admits a
degree-`b` source map that is epimorphic on top cohomology, receives no
nonzero maps from that cohomology object, and composes trivially with the given
morphism. -/
theorem exists_shifted_map_with_zero_comp
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (hneg : HasEnoughNegativeObjects C) (X X' : DerivedCategory.Bounded C)
    (f : X ⟶ X') (b : ℤ)
    (hX : ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.Bounded.homologyFunctor C i).obj X))
    (hX' : ∀ i : ℤ, b ≤ i →
      IsZero ((DerivedCategory.Bounded.homologyFunctor C i).obj X')) :
    ∃ (N : C)
      (g : (DerivedCategory.Bounded.singleFunctor C b).obj N ⟶ X),
      Epi (topCohomologyMap b X g) ∧
        (∀ h : (DerivedCategory.Bounded.homologyFunctor C b).obj X ⟶ N, h = 0) ∧
          g ≫ f = 0 := sorry

end CategoryTheory.DerivedCategory.Bounded
