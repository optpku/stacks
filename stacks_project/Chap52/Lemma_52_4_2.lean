/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Lemma_52_4_1
public import ReasLib.RingTheory.ReesAlgebra.Grading.PowerInclusion
import StacksCheckRecall

@[expose] public section

open scoped BigOperators

universe u

/- Lemma 52.4.2 (1): coefficient maps splitting the inclusion of `I ^ c` determine
a unique graded `A`-algebra map from `reesAlgebra (I ^ c)` to the standard graded
polynomial ring, with the prescribed formula on degree-one elements. -/
@[stacks 0EIB] #check
  (ReesAlgebra.Grading.existsUniquePolynomialLift :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ} (I : Ideal A)
      (f : Fin r → I)
      (hgen : Ideal.span (Set.range fun j ↦ (f j : A)) = I)
      (hcd : Ideal.LocalCohomology.dimension I I.fg_of_isNoetherianRing = 1)
      {c : ℕ} (hc : 1 ≤ c) (φ : Fin r → I.powerHom A c)
      (hφ : ∑ j, (f j : A) • φ j = (I ^ c).subtype),
      ∃! Φ : ReesAlgebra.Grading.grade (I ^ c) →ₐᵍ[A]
          MvPolynomial.standardGrading (Fin r) A,
        ∀ g : (I ^ c : Ideal A),
          Φ (ReesAlgebra.Grading.degreeOne (I ^ c) g) =
            ∑ j, MvPolynomial.C (φ j g) * MvPolynomial.X j)

/- Lemma 52.4.2 (2): any graded map with the prescribed degree-one formula composes
with evaluation at the generators to the canonical inclusion from `reesAlgebra (I ^ c)`
to `reesAlgebra I`. -/
@[stacks 0EIB] #check
  (ReesAlgebra.Grading.polynomialLift_comp_toRees :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ} (I : Ideal A)
      (f : Fin r → I)
      (hgen : Ideal.span (Set.range fun j ↦ (f j : A)) = I)
      (hcd : Ideal.LocalCohomology.dimension I I.fg_of_isNoetherianRing = 1)
      {c : ℕ} (hc : 1 ≤ c) (φ : Fin r → I.powerHom A c)
      (hφ : ∑ j, (f j : A) • φ j = (I ^ c).subtype)
      (Φ : ReesAlgebra.Grading.grade (I ^ c) →ₐᵍ[A]
        MvPolynomial.standardGrading (Fin r) A)
      (hΦ : ∀ g : (I ^ c : Ideal A),
        Φ (ReesAlgebra.Grading.degreeOne (I ^ c) g) =
          ∑ j, MvPolynomial.C (φ j g) * MvPolynomial.X j),
      (ReesAlgebra.Presentation.toRees f).comp Φ.toAlgHom =
        (ReesAlgebra.Grading.powerInclusion I hc).toAlgHom)
