/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Algebra
public import Mathlib.RingTheory.Adjoin.Basic

/-!
# Section algebras on projective basic opens

The section algebra on a positive-degree homogeneous basic open is canonically the
degree-zero homogeneous localization. Fractions of degree-`d` monomials by the defining
form generate this algebra with at most `Nat.choose (n + d) n` generators.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable {R : Type u} [CommRing R]

/-- The canonical localization-to-sections isomorphism on a positive-degree homogeneous
basic open respects the coefficient map from the base ring. -/
theorem basicOpenIsoAway_algebraMap (n d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F ∈ grading R n d)
    (hd : 0 < d) (x : R) :
    (Proj.basicOpenIsoAway (grading R n) F hF hd).hom.hom
        (algebraMap R (HomogeneousLocalization.Away (grading R n) F) x) =
      Scheme.Hom.sectionsMap (toSpec R n) (basicOpen n F) x :=
  sorry

/-- The degree-zero homogeneous localization is canonically isomorphic as a base-ring
algebra to the sections on the corresponding projective basic open. -/
def basicOpenSectionsAlgEquiv (n d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F ∈ grading R n d) (hd : 0 < d) :
    HomogeneousLocalization.Away (grading R n) F ≃ₐ[R]
      Scheme.Hom.sectionsAlgOverSpec (toSpec R n) (basicOpen n F) :=
  { (Proj.basicOpenIsoAway (grading R n) F hF hd).commRingCatIsoToRingEquiv with
    commutes' := fun x ↦ basicOpenIsoAway_algebraMap n d F hF hd x }

/-- The canonical algebra equivalence evaluates by the forward map of the
localization-to-sections ring isomorphism. -/
theorem basicOpenSectionsAlgEquiv_apply (n d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F ∈ grading R n d) (hd : 0 < d)
    (z : HomogeneousLocalization.Away (grading R n) F) :
    basicOpenSectionsAlgEquiv n d F hF hd z =
      (Proj.basicOpenIsoAway (grading R n) F hF hd).hom.hom z :=
  rfl

/-- The degree-zero localization away from a positive-degree homogeneous form in
`n + 1` variables is generated over the coefficient ring by at most
`Nat.choose (n + d) n` elements. -/
theorem exists_away_adjoin_card_le (n d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F ∈ grading R n d) (hd : 0 < d) :
    ∃ s : Finset (HomogeneousLocalization.Away (grading R n) F),
      s.card ≤ Nat.choose (n + d) n ∧
        Algebra.adjoin R (s : Set (HomogeneousLocalization.Away (grading R n) F)) = ⊤ :=
  sorry

/-- The section algebra on the basic open of a degree-`d` homogeneous form in projective
`n`-space is generated over the base ring by at most `Nat.choose (n + d) n` elements. -/
theorem exists_sections_adjoin_card_le (n d : ℕ)
    (F : MvPolynomial (Fin (n + 1)) R) (hF : F ∈ grading R n d) (hd : 0 < d) :
    ∃ s : Finset (Scheme.Hom.sectionsAlgOverSpec (toSpec R n) (basicOpen n F)),
      s.card ≤ Nat.choose (n + d) n ∧
        Algebra.adjoin R
          (s : Set (Scheme.Hom.sectionsAlgOverSpec (toSpec R n) (basicOpen n F))) = ⊤ :=
  sorry

end AlgebraicGeometry.ProjectiveSpace
