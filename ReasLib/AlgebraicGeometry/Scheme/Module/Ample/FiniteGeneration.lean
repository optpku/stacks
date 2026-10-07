module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Characterization
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent

/-!
# Finite generation from ampleness

This file records finite tensor-power presentations of coherent modules by powers of an ample
invertible module.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsAmple

variable {X : Scheme.{u}}

/-- A coherent module is an epimorphic image of a finite coproduct of integral powers of an
ample invertible module. -/
@[stacks 0B5T "finite tensor-power presentation from ampleness"]
theorem exists_epi_from_tensorPowers
    {L : X.Modules} [L.Invertible] (hL : IsAmple L)
    (F : X.Modules) [F.IsCoherent] :
    ∃ (r : ℕ) (d : Fin r → ℤ)
      (π : (∐ fun j : Fin r ↦ L ^⊗ d j) ⟶ F), Epi π := sorry

end AlgebraicGeometry.Scheme.Modules.IsAmple
