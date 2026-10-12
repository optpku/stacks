/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein

@[expose] public section

universe u

#check
  (IsGorensteinLocalRing :
    (R : Type u) → [CommRing R] → [IsLocalRing R] → Prop)

#check
  (IsGorensteinLocalRing.instIsNoetherianRing :
    (R : Type u) → [CommRing R] → [IsLocalRing R] →
      [IsGorensteinLocalRing R] → IsNoetherianRing R)

#check
  (IsGorensteinLocalRing.iff_isNoetherian_and_finiteSelfInjectiveDimension :
    (R : Type u) → [CommRing R] → [IsLocalRing R] →
      IsGorensteinLocalRing R ↔
        IsNoetherianRing R ∧
          CategoryTheory.injectiveDimension (ModuleCat.of R R) ≠ ⊤)

#check
  (AlgebraicGeometry.Scheme.Gorenstein : AlgebraicGeometry.Scheme.{u} → Prop)

#check
  (AlgebraicGeometry.Scheme.Gorenstein.instIsLocallyNoetherian :
    (X : AlgebraicGeometry.Scheme.{u}) →
      [AlgebraicGeometry.Scheme.Gorenstein X] →
        AlgebraicGeometry.IsLocallyNoetherian X)

#check
  (AlgebraicGeometry.Scheme.gorenstein_iff :
    (X : AlgebraicGeometry.Scheme.{u}) →
      AlgebraicGeometry.Scheme.Gorenstein X ↔
        AlgebraicGeometry.IsLocallyNoetherian X ∧
          ∀ x : X, IsGorensteinLocalRing (X.presheaf.stalk x))
