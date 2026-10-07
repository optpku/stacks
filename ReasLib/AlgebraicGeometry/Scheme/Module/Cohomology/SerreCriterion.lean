module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AmpleCriterion
import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffineCover

/-!
# Serre's cohomological criterion for ampleness

This file characterizes ample invertible modules on schemes proper over Noetherian affine bases
by eventual vanishing of positive-degree cohomology and by first-cohomology vanishing for
positive twists of quasi-coherent ideal sheaves.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- For an invertible module on a scheme proper over a Noetherian affine base, ampleness is
equivalent to eventual vanishing of every coherent module's positive-degree cohomology after
high positive twists, and to positive-twist first-cohomology vanishing for every quasi-coherent
ideal sheaf. -/
@[stacks 0B5U]
theorem isAmple_tfae_eventual_positive_twist_cohomology_and_ideal_H1
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (L : X.Modules) [Invertible L] :
    List.TFAE
      [ IsAmple L,
        ∀ F : X.Modules, F.IsCoherent →
          ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ p : ℕ, 0 < p →
            IsZero (RingedSpace.moduleCohomology
              (F ⊗ RingedSpace.TensorPower.sheaf L n) p),
        ∀ I : Scheme.IdealSubobject X, I.toModule.IsQuasicoherent →
          ∃ n : ℕ, 0 < n ∧
            IsZero (RingedSpace.moduleCohomology
              (I.toModule ⊗ RingedSpace.TensorPower.sheaf L n) 1) ] := sorry

end AlgebraicGeometry.Scheme.Modules
