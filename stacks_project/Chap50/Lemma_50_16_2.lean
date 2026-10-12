/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.CoordinateCenter.ExceptionalPoleComparison
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 50.16.2: for every `a : ℕ`, the composite of the canonical maps
`b^* Ω^a_{X/S} ⟶ Ω^a_{L/S}` and
`Ω^a_{L/S} ⟶ b^* Ω^a_{X/S} ⊗ 𝒪_L((n - 1)E)` is tensoring with the canonical inclusion
`𝒪_L ⟶ 𝒪_L((n - 1)E)`. -/
@[stacks 0G5G] #check (AlgebraicGeometry.Blowup.CoordinateCenter.formComparison_exceptionalPoleComparison :
    ∀ (R : Type u) [CommRing R] (m n : ℕ) [NeZero n]
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
    (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))))
    (a : ℕ),
    Scheme.RelativeDifferentials.formComparison
          (CommSq.mk (Category.comp_id _).symm) a ≫
        AlgebraicGeometry.Blowup.CoordinateCenter.exceptionalPoleComparison R m n π a =
      ((ρ_ ((Scheme.Modules.pullback π.hom).obj
        (Λ[a] Ω[(Spec.map
            (CommRingCat.ofHom
              (algebraMap R
                (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom]))).inv ≫
        tensorHom (𝟙 _)
          ((RingedSpace.unitIsoTensorUnit π.scheme.toRingedSpace).inv ≫
            π.exceptionalTwistSectionHom (n - 1))))
