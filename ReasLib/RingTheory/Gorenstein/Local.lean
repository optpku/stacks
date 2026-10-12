/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalProperties.InjectiveDimension

@[expose] public section

universe u

/-- A commutative local ring is Gorenstein if it is Noetherian and has finite injective
dimension as a module over itself. -/
class IsGorensteinLocalRing (R : Type u) [CommRing R] [IsLocalRing R] : Prop where
  /-- A Gorenstein local ring is Noetherian. -/
  isNoetherian : IsNoetherianRing R
  /-- The ring has finite injective dimension as a module over itself. -/
  finiteSelfInjectiveDimension :
    CategoryTheory.injectiveDimension (ModuleCat.of R R) ≠ ⊤

namespace IsGorensteinLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- A Gorenstein local ring carries its canonical Noetherian-ring instance. -/
instance instIsNoetherianRing [h : IsGorensteinLocalRing R] : IsNoetherianRing R :=
  h.isNoetherian

/-- The defining conditions for a Gorenstein local ring. -/
theorem iff_isNoetherian_and_finiteSelfInjectiveDimension :
    IsGorensteinLocalRing R ↔
      IsNoetherianRing R ∧
        CategoryTheory.injectiveDimension (ModuleCat.of R R) ≠ ⊤ := sorry

end IsGorensteinLocalRing
