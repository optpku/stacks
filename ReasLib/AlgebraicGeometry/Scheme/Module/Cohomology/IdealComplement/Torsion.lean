/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.IdealComplement

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IdealComplement

/-- Positive-degree cohomology on the complement of the vanishing locus of a finitely
generated ideal is power-torsion for that ideal. -/
theorem isIdealPowerTorsion_cohomology {A : Type u} [CommRing A] {t : ℕ}
    (f : Fin t → A) (F : (Spec (CommRingCat.of A)).Modules) [F.IsQuasicoherent]
    {p : ℕ} (hp : 0 < p) :
    Module.IsIdealPowerTorsion (Ideal.span (Set.range f))
      (cohomology (Ideal.span (Set.range f))
        (F.restrict (idealComplementOpens (Ideal.span (Set.range f))).ι) p) := sorry

/-- Every positive-degree cohomology class on an affine ideal complement is annihilated
by a common positive power of each member of a finite generating family. -/
theorem exists_pow_smul_eq_zero {A : Type u} [CommRing A] {t : ℕ}
    (f : Fin t → A) (F : (Spec (CommRingCat.of A)).Modules) [F.IsQuasicoherent]
    {p : ℕ} (hp : 0 < p)
    (ξ : cohomology (Ideal.span (Set.range f))
      (F.restrict (idealComplementOpens (Ideal.span (Set.range f))).ι) p) :
    ∃ n : ℕ, 0 < n ∧ ∀ i : Fin t, (f i) ^ n • ξ = 0 := sorry

end AlgebraicGeometry.Scheme.Modules.IdealComplement
