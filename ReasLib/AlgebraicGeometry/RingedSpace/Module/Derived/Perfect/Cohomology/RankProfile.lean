/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Cohomology.FiniteFreeLocus

@[expose] public section

open AlgebraicGeometry CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

variable {X : RingedSpace.{u}}
variable {E : ModuleDerived X}

/-- The cohomology sheaves of `E` have the integer rank profile `ρ` on `U`. -/
def rankProfileOn (E : ModuleDerived X) (ρ : ℤ → ℤ) (U : Opens X.carrier) : Prop :=
  U = ⊥ ∨
    ∀ i : ℤ, 0 ≤ ρ i ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank (ρ i).toNat
        ((DerivedCategory.homologyFunctor
          (RingedSpace.Modules (X.restrict U.isOpenEmbedding)) i).obj
            ((RingedSpace.moduleRestrictionToOpenDerived X U).obj E))

/-- The integer-rank profile condition is vacuous on the empty open; otherwise it is the
conjunction of nonnegativity and the degreewise finite-locally-free rank conditions. -/
theorem rankProfileOn_iff (E : ModuleDerived X) (ρ : ℤ → ℤ) (U : Opens X.carrier) :
    rankProfileOn E ρ U ↔ U = ⊥ ∨
      ∀ i : ℤ, 0 ≤ ρ i ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank (ρ i).toNat
          ((DerivedCategory.homologyFunctor
            (RingedSpace.Modules (X.restrict U.isOpenEmbedding)) i).obj
              ((RingedSpace.moduleRestrictionToOpenDerived X U).obj E)) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Cohomology

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}
variable {E : ModuleDerived X}

/-- The maximal open on which a perfect derived module has the prescribed integer rank profile. -/
def IsPerfect.rankProfileOpen (hE : IsPerfect E) (ρ : ℤ → ℤ) : Opens X.carrier :=
  sSup {U : Opens X.carrier | Cohomology.rankProfileOn E ρ U}

/-- An open has the prescribed cohomology rank profile exactly when it is contained in the
maximal rank-profile open of a perfect derived module. -/
theorem IsPerfect.rankProfileOn_iff_le_rankProfileOpen
    (hE : IsPerfect E) (ρ : ℤ → ℤ) (U : Opens X.carrier) :
    Cohomology.rankProfileOn E ρ U ↔ U ≤ hE.rankProfileOpen ρ := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
