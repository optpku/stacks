/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.SerreCriterion
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

/- Lemma 30.17.1: for a proper morphism `X → Spec(R)` with `R` Noetherian and an invertible
`𝒪_X`-module `L`, ampleness of `L`, eventual vanishing of higher cohomology after high
positive twists for every coherent module, and positive-twist `H^1`-vanishing for every
quasi-coherent ideal sheaf are equivalent. -/
@[stacks 0B5U] #check
  (AlgebraicGeometry.Scheme.Modules.isAmple_tfae_eventual_positive_twist_cohomology_and_ideal_H1 :
    ∀ {X : Scheme.{u}}
      [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
      {R : Type u} [CommRing R] [IsNoetherianRing R]
      (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
      (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L],
      List.TFAE
        [ Scheme.Modules.IsAmple L,
          ∀ F : X.Modules, F.IsCoherent →
            ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ p : ℕ, 0 < p →
              IsZero (RingedSpace.moduleCohomology
                (F ⊗ RingedSpace.TensorPower.sheaf L n) p),
          ∀ I : Scheme.IdealSubobject X, I.toModule.IsQuasicoherent →
            ∃ n : ℕ, 0 < n ∧
              IsZero (RingedSpace.moduleCohomology
                (I.toModule ⊗ RingedSpace.TensorPower.sheaf L n) 1) ])
