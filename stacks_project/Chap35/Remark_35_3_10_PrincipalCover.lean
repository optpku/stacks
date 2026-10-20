/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Spec.BasicOpen.FaithfullyFlat

@[expose] public section

universe u v

/- The faithfully flat principal-localization product theorem is provided by its reusable
mathematical owner. -/
#check
  (AlgebraicGeometry.Spec.BasicOpenUnion.localizationProductMap_faithfullyFlat :
    ∀ {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R),
      Ideal.span (Set.range f) = ⊤ →
        (AlgebraicGeometry.Spec.BasicOpenUnion.localizationProductMap f).FaithfullyFlat)

/- The unit-ideal vanishing theorem for extended alternating Cech cohomology is provided by its
reusable mathematical owner. -/
#check
  (LocalizedModule.Away.Cech.Alternating.Cohomology.isZero_of_span_eq_top :
    ∀ {R : Type u} [CommRing R]
      {M : Type (max u v)} [AddCommGroup M] [Module R M] {r : ℕ}
      (f : Fin r → R), Ideal.span (Set.range f) = ⊤ → ∀ q : ℕ,
        CategoryTheory.Limits.IsZero
          ((LocalizedModule.Away.Cech.Alternating.extended f M).homology q))
