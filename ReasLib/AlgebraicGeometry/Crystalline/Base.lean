/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.RingTheory.Localization.AtPrime.Int

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

/-- A prime-local relative crystalline base consists of a divided-power scheme,
its structure morphism over the `p`-local integers, and a locally nilpotent
scheme over its canonical closed subscheme. -/
structure Base (p : ℕ) [Fact p.Prime] : Type (u + 1) where
  /-- The ambient scheme carrying the divided-power ideal sheaf. -/
  scheme : Scheme.{u}
  /-- The affine-section data of the quasi-coherent ideal sheaf. -/
  ideal : scheme.IdealSheafData
  /-- The ideal sheaf is quasi-coherent. -/
  quasiCoherent : ideal.toModule.IsQuasicoherent
  /-- The divided-power structure on each affine section of the ideal sheaf. -/
  dividedPowers : ∀ V : scheme.affineOpens, DividedPowers (ideal.ideal V)
  /-- The divided powers are preserved by restriction to every basic open. -/
  compatible :
    ∀ (V : scheme.affineOpens) (f : Γ(scheme, V)),
      (dividedPowers V).IsDPMorphism (dividedPowers (scheme.affineBasicOpen f))
        (scheme.presheaf.map (homOfLE (scheme.basicOpen_le f)).op).hom
  /-- The structure morphism to the spectrum of the `p`-local integers. -/
  toSpec : scheme ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))
  /-- The scheme lying over the canonical closed subscheme. -/
  source : Scheme.{u}
  /-- The morphism from the source scheme to the canonical closed subscheme. -/
  sourceToClosed : source ⟶ ideal.subscheme
  /-- The prime `p` is nilpotent on every affine open section of the source. -/
  prime_nilpotent : ∀ U : source.affineOpens, IsNilpotent (p : Γ(source, U))

/-- Construct a prime-local relative crystalline base from its constituent data. -/
def Base.of (p : ℕ) [Fact p.Prime] (scheme : Scheme.{u})
    (ideal : scheme.IdealSheafData)
    (quasiCoherent : ideal.toModule.IsQuasicoherent)
    (dividedPowers : ∀ V : scheme.affineOpens, DividedPowers (ideal.ideal V))
    (compatible :
      ∀ (V : scheme.affineOpens) (f : Γ(scheme, V)),
        (dividedPowers V).IsDPMorphism (dividedPowers (scheme.affineBasicOpen f))
          (scheme.presheaf.map (homOfLE (scheme.basicOpen_le f)).op).hom)
    (toSpec : scheme ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (source : Scheme.{u}) (sourceToClosed : source ⟶ ideal.subscheme)
    (prime_nilpotent : ∀ U : source.affineOpens, IsNilpotent (p : Γ(source, U))) :
    Base p where
  scheme := scheme
  ideal := ideal
  quasiCoherent := quasiCoherent
  dividedPowers := dividedPowers
  compatible := compatible
  toSpec := toSpec
  source := source
  sourceToClosed := sourceToClosed
  prime_nilpotent := prime_nilpotent

/-- The quasi-coherence, restriction compatibility, and local nilpotence conditions of a
prime-local relative crystalline base. -/
theorem Base.spec (p : ℕ) [Fact p.Prime] (B : Base p) :
    B.ideal.toModule.IsQuasicoherent ∧
    (∀ (V : B.scheme.affineOpens) (f : Γ(B.scheme, V)),
      (B.dividedPowers V).IsDPMorphism
        (B.dividedPowers (B.scheme.affineBasicOpen f))
        (B.scheme.presheaf.map (homOfLE (B.scheme.basicOpen_le f)).op).hom) ∧
      ∀ U : B.source.affineOpens, IsNilpotent (p : Γ(B.source, U)) := sorry

/-- Replace the source of a crystalline base while retaining its divided-power base. -/
@[reducible]
def Base.withSource {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
    (X : Scheme.{u}) (x₀ : X ⟶ B.ideal.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) : Base p :=
  { B with source := X, sourceToClosed := x₀, prime_nilpotent := h_p }

/-- If the prime lies in the defining ideal, it is nilpotent on every affine open of
any scheme over the associated closed subscheme. -/
theorem Base.prime_nilpotent_of_mem {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
    (h_p_mem : ∀ V : B.scheme.affineOpens, (p : Γ(B.scheme, V)) ∈ B.ideal.ideal V)
    (X : Scheme.{u}) (x₀ : X ⟶ B.ideal.subscheme) :
    ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)) := sorry

end AlgebraicGeometry.Scheme.Crystalline
