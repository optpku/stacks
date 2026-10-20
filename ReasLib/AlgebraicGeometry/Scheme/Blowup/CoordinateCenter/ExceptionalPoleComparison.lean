/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.CoordinateCenter
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ExceptionalTwist
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.ExteriorPower.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import Mathlib.RingTheory.MvPolynomial.Ideal

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Blowup.CoordinateCenter

/-- The canonical comparison from differential forms on a coordinate-center blowup to pulled-back
forms twisted by the exceptional divisor. -/
noncomputable def exceptionalPoleComparison
    (R : Type u) [CommRing R] (m n : ℕ) [NeZero n]
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))))
    (a : ℕ) :
    (Λ[a] Ω[(π.hom ≫ Spec.map
      (CommRingCat.ofHom
        (algebraMap R (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom]) ⟶
      (Scheme.Modules.pullback π.hom).obj
          (Λ[a] Ω[(Spec.map
            (CommRingCat.ofHom
              (algebraMap R
                (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom]) ⊗
        π.exceptionalTwist (n - 1) :=
  Classical.epsilon fun poleMap ↦
    Scheme.RelativeDifferentials.formComparison
          (CommSq.mk (Category.comp_id _).symm) a ≫ poleMap =
      ((ρ_ ((Scheme.Modules.pullback π.hom).obj
        (Λ[a] Ω[(Spec.map
            (CommRingCat.ofHom
              (algebraMap R
                (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom]))).inv ≫
        tensorHom (𝟙 _)
          ((RingedSpace.unitIsoTensorUnit π.scheme.toRingedSpace).inv ≫
            π.exceptionalTwistSectionHom (n - 1)))

/-- The differential-form comparison followed by the exceptional-pole comparison is induced by
the canonical inclusion into the exceptional twist. -/
theorem formComparison_exceptionalPoleComparison
    (R : Type u) [CommRing R] (m n : ℕ) [NeZero n]
    (π : Blowup
      (Spec (.of (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))
      (Scheme.idealSheafDataOfIdealOnSpec
        (MvPolynomial.idealOfVars (Fin n) (MvPolynomial (Fin m) R))))
    (a : ℕ) :
    Scheme.RelativeDifferentials.formComparison
          (CommSq.mk (Category.comp_id _).symm) a ≫
        exceptionalPoleComparison R m n π a =
      ((ρ_ ((Scheme.Modules.pullback π.hom).obj
        (Λ[a] Ω[(Spec.map
            (CommRingCat.ofHom
              (algebraMap R
                (MvPolynomial (Fin n) (MvPolynomial (Fin m) R))))).toShHom]))).inv ≫
        tensorHom (𝟙 _)
          ((RingedSpace.unitIsoTensorUnit π.scheme.toRingedSpace).inv ≫
            π.exceptionalTwistSectionHom (n - 1))) := sorry

end AlgebraicGeometry.Blowup.CoordinateCenter
