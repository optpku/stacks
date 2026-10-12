/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Biproduct
public import Mathlib.CategoryTheory.IsomorphismClasses

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A scheme module is split when it is isomorphic to a finite biproduct of invertible
scheme modules. -/
class IsSplit {X : Scheme.{u}} (E : X.Modules) : Prop where
  /-- A split module is isomorphic to a finite biproduct of invertible modules. -/
  exists_iso :
    ∃ (n : ℕ) (L : Fin n → X.Modules),
      (∀ i, Invertible (L i)) ∧ IsIsomorphic E (biproduct L)

/-- Split scheme modules are precisely those isomorphic to a finite biproduct of invertibles. -/
theorem isSplit_iff {X : Scheme.{u}} (E : X.Modules) :
    IsSplit E ↔
      ∃ (n : ℕ) (L : Fin n → X.Modules),
        (∀ i, Invertible (L i)) ∧ IsIsomorphic E (biproduct L) := sorry

/-- An invertible scheme module is split. -/
instance instIsSplit_of_invertible {X : Scheme.{u}} (E : X.Modules) [Invertible E] :
    IsSplit E := sorry

/-- A finite biproduct of invertible scheme modules is split. -/
instance instIsSplit_biproduct {X : Scheme.{u}} {n : ℕ} (L : Fin n → X.Modules)
    [∀ i, Invertible (L i)] : IsSplit (biproduct L) := sorry

end AlgebraicGeometry.Scheme.Modules
