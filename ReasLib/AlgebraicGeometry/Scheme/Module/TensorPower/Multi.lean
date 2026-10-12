/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent

/-!
# Finite families of tensor twists

This leaf packages the ordered tensor product of integral powers of a finite
family of invertible scheme modules.  It is independent of intersection
theory and can therefore be reused by Hilbert-polynomial and section-ring
arguments.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.TensorPower

variable {X : Scheme.{u}}

/-- The ordered tensor twist of a scheme module by integral powers of a finite family of
invertible modules. -/
noncomputable def multiTwist
    (F : X.Modules) {r : ℕ} (L : Fin r → X.Modules)
    [∀ j : Fin r, Invertible (L j)] (n : Fin r → ℤ) : X.Modules :=
  (List.finRange r).foldl
    (fun acc j ↦ tensorObj acc (tensorPowerInt (L j) (n j))) F

/-- The ordered fold expression defining `multiTwist`. -/
theorem multiTwist_def
    (F : X.Modules) {r : ℕ} (L : Fin r → X.Modules)
    [∀ j : Fin r, Invertible (L j)] (n : Fin r → ℤ) :
    multiTwist F L n =
      (List.finRange r).foldl
        (fun acc j ↦ tensorObj acc (tensorPowerInt (L j) (n j))) F := sorry

/-- Tensoring a coherent scheme module by a finite family of invertible powers preserves
coherence. -/
theorem isCoherent_multiTwist
    (F : X.Modules) [F.IsCoherent] {r : ℕ} (L : Fin r → X.Modules)
    [∀ j : Fin r, Invertible (L j)] (n : Fin r → ℤ) :
    (multiTwist F L n).IsCoherent := sorry

attribute [instance] isCoherent_multiTwist

end AlgebraicGeometry.Scheme.Modules.TensorPower
