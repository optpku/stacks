/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension.IdealPowerLift
public import ReasLib.RingTheory.MvPolynomial.StandardGrading
public import ReasLib.RingTheory.ReesAlgebra.Presentation

@[expose] public section

noncomputable section

open scoped BigOperators

universe u

namespace ReesAlgebra.Grading

variable {A : Type u} [CommRing A]

/-- A positive power of an ideal is contained in the ideal. -/
theorem power_le_self (I : Ideal A) {c : ℕ} (hc : 1 ≤ c) : I ^ c ≤ I := sorry

/-- The inclusion of a positive ideal power is compatible with the identity map of the ring. -/
theorem powerInclusion_comap (I : Ideal A) {c : ℕ} (hc : 1 ≤ c) :
    I ^ c ≤ Ideal.comap (RingHom.id A) I := sorry

/-- The graded Rees map induced by inclusion of a positive ideal power is `A`-linear. -/
theorem powerInclusion_smul (I : Ideal A) {c : ℕ} (hc : 1 ≤ c)
    (a : A) (x : reesAlgebra (I ^ c)) :
    gradedMap (RingHom.id A) (I ^ c) I (hIJ := powerInclusion_comap I hc) (a • x) =
      a • gradedMap (RingHom.id A) (I ^ c) I
        (hIJ := powerInclusion_comap I hc) x := sorry

/-- The canonical graded `A`-algebra inclusion from the Rees algebra of a positive
power `I ^ c` into the Rees algebra of `I`. -/
noncomputable def powerInclusion (I : Ideal A) {c : ℕ} (hc : 1 ≤ c) :
    grade (I ^ c) →ₐᵍ[A] grade I :=
  GradedAlgHom.mk'
    (gradedMap (RingHom.id A) (I ^ c) I (hIJ := powerInclusion_comap I hc))
    (powerInclusion_smul I hc)

/-- The polynomial underlying `powerInclusion I hc x` is the polynomial underlying `x`. -/
theorem powerInclusion_apply (I : Ideal A) {c : ℕ} (hc : 1 ≤ c)
    (x : reesAlgebra (I ^ c)) :
    (powerInclusion I hc x).1 = x.1 := sorry

/-- The inclusion of Rees algebras sends a degree-one element to the same coefficient
viewed as an element of `I`. -/
theorem powerInclusion_degreeOne (I : Ideal A) {c : ℕ} (hc : 1 ≤ c)
    (g : (I ^ c : Ideal A)) :
    powerInclusion I hc (degreeOne (I ^ c) g) =
      degreeOne I ⟨g.1, power_le_self I hc g.2⟩ := sorry

section LocalCohomology

variable [IsNoetherianRing A]

/-- A splitting of the inclusion `I ^ c ⟶ A` determines a unique graded map from
the Rees algebra of `I ^ c` to the standard graded polynomial ring. -/
theorem existsUniquePolynomialLift {r : ℕ} (I : Ideal A) (f : Fin r → I)
    (hgen : Ideal.span (Set.range fun j ↦ (f j : A)) = I)
    (hcd : Ideal.LocalCohomology.dimension I I.fg_of_isNoetherianRing = 1)
    {c : ℕ} (hc : 1 ≤ c) (φ : Fin r → I.powerHom A c)
    (hφ : ∑ j, (f j : A) • φ j = (I ^ c).subtype) :
    ∃! Φ : grade (I ^ c) →ₐᵍ[A] MvPolynomial.standardGrading (Fin r) A,
      ∀ g : (I ^ c : Ideal A),
        Φ (degreeOne (I ^ c) g) =
          ∑ j, MvPolynomial.C (φ j g) * MvPolynomial.X j := sorry

/-- Every graded polynomial lift with the prescribed degree-one formula composes with
Rees evaluation to the canonical inclusion of the positive ideal power. -/
theorem polynomialLift_comp_toRees {r : ℕ} (I : Ideal A) (f : Fin r → I)
    (hgen : Ideal.span (Set.range fun j ↦ (f j : A)) = I)
    (hcd : Ideal.LocalCohomology.dimension I I.fg_of_isNoetherianRing = 1)
    {c : ℕ} (hc : 1 ≤ c) (φ : Fin r → I.powerHom A c)
    (hφ : ∑ j, (f j : A) • φ j = (I ^ c).subtype)
    (Φ : grade (I ^ c) →ₐᵍ[A] MvPolynomial.standardGrading (Fin r) A)
    (hΦ : ∀ g : (I ^ c : Ideal A),
      Φ (degreeOne (I ^ c) g) =
        ∑ j, MvPolynomial.C (φ j g) * MvPolynomial.X j) :
    (ReesAlgebra.Presentation.toRees f).comp Φ.toAlgHom =
      (powerInclusion I hc).toAlgHom := sorry

end LocalCohomology

end ReesAlgebra.Grading
