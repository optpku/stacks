/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject

open CategoryTheory AlgebraicGeometry SheafOfModules

@[expose] public section

/-- A divided power scheme consists of a scheme, a quasi-coherent ideal sheaf,
divided powers on the ideals of affine sections, and compatibility with
restriction to basic opens. -/
structure DividedPowerScheme where
  /-- The underlying scheme. -/
  scheme : Scheme.{u}
  /-- The ideal sheaf on the underlying scheme. -/
  ideal : scheme.IdealSheafData
  /-- The ideal sheaf is quasi-coherent. -/
  quasiCoherent : ideal.toModule.IsQuasicoherent
  /-- Divided powers on the ideal over every affine open. -/
  dividedPowers : ∀ V : scheme.affineOpens, DividedPowers (ideal.ideal V)
  /-- Restriction maps preserve the divided-power operations. -/
  compatible :
    ∀ (V : scheme.affineOpens) (f : Γ(scheme, V)),
      (dividedPowers V).IsDPMorphism
        (dividedPowers (scheme.affineBasicOpen f))
        (scheme.presheaf.map (homOfLE (scheme.basicOpen_le f)).op).hom

namespace DividedPowerScheme

universe u

/-- Construct a divided power scheme from its underlying scheme, quasi-coherent
ideal sheaf, divided powers, and restriction compatibility. -/
def of (S : Scheme.{u}) (I : S.IdealSheafData)
    (h_quasiCoherent : I.toModule.IsQuasicoherent)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom) :
    DividedPowerScheme :=
  { scheme := S
    ideal := I
    quasiCoherent := h_quasiCoherent
    dividedPowers := γ
    compatible := h_compatible }

/-- A divided power scheme has a quasi-coherent ideal sheaf and its
divided-power operations commute with restriction to basic opens. -/
theorem spec (X : DividedPowerScheme.{u}) :
    let S := X.scheme
    (type_of% X.quasiCoherent) ∧
      (∀ (V : S.affineOpens) (f : Γ(S, V)),
        (X.dividedPowers V).IsDPMorphism
          (X.dividedPowers (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom) := sorry

/-- A morphism of divided power schemes consists of a scheme morphism whose
pullback ideal is contained in the source ideal and whose affine-section maps
are divided-power morphisms. -/
structure Hom (X Y : DividedPowerScheme.{u}) where
  /-- The underlying morphism of schemes. -/
  base : X.scheme ⟶ Y.scheme
  /-- The pullback of the target ideal is contained in the source ideal. -/
  ideal_compatible : Y.ideal.comap base ≤ X.ideal
  /-- The induced maps on affine sections preserve divided powers. -/
  dividedPowers_compatible :
    ∀ (V : Y.scheme.affineOpens) (W : X.scheme.affineOpens)
      (hVW : W.1 ≤ base ⁻¹ᵁ V.1),
      (Y.dividedPowers V).IsDPMorphism (X.dividedPowers W)
        (base.appLE V.1 W.1 hVW).hom

namespace Hom

/-- Construct a morphism of divided power schemes from its map of schemes and
the two compatibility conditions. -/
def of {X Y : DividedPowerScheme.{u}} (base : X.scheme ⟶ Y.scheme)
    (h_ideal : Y.ideal.comap base ≤ X.ideal)
    (h_dividedPowers :
      ∀ (V : Y.scheme.affineOpens) (W : X.scheme.affineOpens)
        (hVW : W.1 ≤ base ⁻¹ᵁ V.1),
        (Y.dividedPowers V).IsDPMorphism (X.dividedPowers W)
          (base.appLE V.1 W.1 hVW).hom) :
    Hom X Y :=
  { base := base
    ideal_compatible := h_ideal
    dividedPowers_compatible := h_dividedPowers }

/-- A morphism of divided power schemes preserves the ideal sheaves and
divided-power operations on affine sections. -/
theorem spec {X Y : DividedPowerScheme.{u}} (f : Hom X Y) :
    Y.ideal.comap f.base ≤ X.ideal ∧
      (∀ (V : Y.scheme.affineOpens) (W : X.scheme.affineOpens)
        (hVW : W.1 ≤ f.base ⁻¹ᵁ V.1),
        (Y.dividedPowers V).IsDPMorphism (X.dividedPowers W)
          (f.base.appLE V.1 W.1 hVW).hom) := sorry

end Hom

end DividedPowerScheme
