module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ample Invertible Module Sheaves on Schemes

This file owns the scheme-level definition of ampleness. Ampleness adds quasi-compactness and
affine-neighborhood requirements to the nonvanishing-open theory of invertible modules.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- An affine open neighborhood of a point of a scheme. -/
@[stacks 01PS "affine open neighborhood"]
def AffineOpenNeighborhood (x : X) (U : X.Opens) : Prop :=
  x ∈ (U : Set X) ∧ IsAffineOpen U

/-- An affine open neighborhood is exactly an affine open containing the chosen point. -/
theorem affineOpenNeighborhood_iff (x : X) (U : X.Opens) :
    AffineOpenNeighborhood x U ↔ x ∈ (U : Set X) ∧ IsAffineOpen U := sorry

/-- An invertible module is ample when the scheme is quasi-compact and every point belongs to an
affine nonvanishing open of a positive tensor power. -/
@[stacks 01PS]
class IsAmple (L : X.Modules) [hL : Invertible L] : Prop extends CompactSpace X where
  /-- The affine nonvanishing-neighborhood clause of ampleness. -/
  affine_nonvanishing (x : X) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤),
      AffineOpenNeighborhood x (hL.nonvanishingOpen s)

/-- The object property of being an ample invertible module for the canonical tensor product. -/
@[stacks 01PS "ample invertible module object property"]
def isAmpleObject : ObjectProperty X.Modules :=
  fun L ↦ ∃ hL : Invertible L, @IsAmple X L hL

/-- A module belongs to `isAmpleObject` exactly when it has compatible invertibility and
ampleness witnesses. -/
theorem isAmpleObject_iff (L : X.Modules) :
    isAmpleObject L ↔ ∃ hL : Invertible L, @IsAmple X L hL := sorry

/-- A scheme admits an ample invertible module for its canonical module tensor product. -/
@[stacks 01PS "scheme admitting an ample invertible module"]
def HasAmpleInvertibleModule (X : Scheme.{u}) : Prop :=
  ∃ L : X.Modules, isAmpleObject L

/-- Ampleness is exactly quasi-compactness together with the affine nonvanishing-neighborhood
condition. -/
theorem isAmple_iff (L : X.Modules) [hL : Invertible L] :
    IsAmple L ↔
      IsCompact (Set.univ : Set X) ∧
        ∀ x : X,
          ∃ n : ℕ, 0 < n ∧ ∃ s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤),
            AffineOpenNeighborhood x (hL.nonvanishingOpen s) := sorry

end AlgebraicGeometry.Scheme.Modules
