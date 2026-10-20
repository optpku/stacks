/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.FormalReesModule
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.CoherentFormalModules
open AlgebraicGeometry.Scheme.Modules
open scoped BigOperators

universe u

/- Lemma 52.4.4: after increasing the exponent and restricting the coefficient maps, a coherent
formal module on a Noetherian scheme has a unique graded polynomial lift of its inverse limit,
whose evaluation at the generators is the canonical inclusion into the ordinary Rees module. -/
@[stacks 0EH6] #check
  (Ideal.LocalCohomology.existsUniqueGradedPolynomialFormalLift :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    {r : ℕ} (I : Ideal A) (a : Fin r → I)
    (hgen : Ideal.span (Set.range fun j ↦ (a j : A)) = I)
    (hcd : Ideal.LocalCohomology.dimension I I.fg_of_isNoetherianRing = 1)
    {c : ℕ} (hc : 1 ≤ c) (φ : Fin r → I.powerHom A c)
    (hφ : ∑ j, (a j : A) • φ j = (I ^ c).subtype)
    {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of A))
    (F : X.CoherentFormalModules
      ((Scheme.idealSheafDataOfIdealOnSpec I).comap f)),
    ∃ (c' : ℕ) (hcc : c ≤ c') (hc' : 1 ≤ c'),
      ∃ φ' : Fin r → I.powerHom A c',
        (∀ j, φ' j = (φ j).comp
          (Submodule.inclusion (Ideal.pow_le_pow_right hcc))) ∧
        (∑ j, (a j : A) • φ' j = (I ^ c').subtype) ∧
        ∃ Φ : ReesAlgebra.Grading.grade (I ^ c') →ₐᵍ[A]
            MvPolynomial.standardGrading (Fin r) A,
          (∀ g : (I ^ c' : Ideal A),
            Φ (ReesAlgebra.Grading.degreeOne (I ^ c') g) =
              ∑ j, MvPolynomial.C (φ' j g) * MvPolynomial.X j) ∧
          (ReesAlgebra.Presentation.toRees a).comp Φ.toAlgHom =
            (ReesAlgebra.Grading.powerInclusion I hc').toAlgHom ∧
          (∃! Ψ : FormalReesModule.powered
                ((Scheme.idealSheafDataOfIdealOnSpec I).comap f)
                (limitModule F) c' ⟶
              FormalReesModule.polynomial r (limitModule F),
            FormalReesModule.IsPolynomialLift I f (limitModule F) Φ Ψ) ∧
          ∀ Ψ : FormalReesModule.powered
                ((Scheme.idealSheafDataOfIdealOnSpec I).comap f)
                (limitModule F) c' ⟶
              FormalReesModule.polynomial r (limitModule F),
            FormalReesModule.IsPolynomialLift I f (limitModule F) Φ Ψ →
              Ψ ≫ FormalReesModule.evaluation I a f (limitModule F) =
                FormalReesModule.powerInclusion
                  ((Scheme.idealSheafDataOfIdealOnSpec I).comap f)
                  (limitModule F) hc')
