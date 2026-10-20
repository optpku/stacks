/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized
public import stacks_project.Chap47.Lemma_47_15_6

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

/- The normalized-dualizing predicate and its API are owned by ReasLib. -/
#check (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (K : DerivedCategory (ModuleCat.{u} A))
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))), Prop)

#check (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.of :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    {K : DerivedCategory (ModuleCat.{u} A)}
    {H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))},
    K.IsDualizingComplex H →
      Nonempty
        (((MonoidalClosed.ihomOf H
          (ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A)))).obj K) ≅
            ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A))) →
      K.IsNormalizedDualizingComplex H)

#check (CategoryTheory.DerivedCategory.isNormalizedDualizingComplex_iff :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (K : DerivedCategory (ModuleCat.{u} A))
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))),
    K.IsNormalizedDualizingComplex H ↔
      K.IsDualizingComplex H ∧
        Nonempty
          (((MonoidalClosed.ihomOf H
            (ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A)))).obj K) ≅
              ModuleCat.single0 (ModuleCat.of A (IsLocalRing.ResidueField A))))

end CategoryTheory.DerivedCategory
