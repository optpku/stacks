/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Base
public import ReasLib.AlgebraicGeometry.Crystalline.StructureSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable {p : ℕ} [Fact p.Prime] (B : Base.{u} p)
  (F : SheafOfModules.{u} (smallStructureSheaf (S := B.scheme) (I := B.ideal)
    (γ := B.dividedPowers) (h_compatible := B.compatible)
    (X := B.source) (x₀ := B.sourceToClosed)))

/-- An `S`-derivation into a sheaf of modules on the small crystalline site is a
natural family of additive Leibniz maps, vanishing on every factoring base open
and respecting divided powers on every affine open restriction. -/
structure SDerivation where
  /-- The additive map on sections over each small crystalline thickening. -/
  component : ∀ T : smallCrystallineSite B.scheme B.ideal B.dividedPowers
      B.compatible B.source B.sourceToClosed,
    Γ(T.obj.1.thickening, ⊤) →+ F.val.obj (op T)
  /-- The section maps commute with every morphism in the small crystalline site. -/
  natural : ∀ {T U : smallCrystallineSite B.scheme B.ideal B.dividedPowers
      B.compatible B.source B.sourceToClosed} (f : T ⟶ U)
      (a : Γ(U.obj.1.thickening, ⊤)),
    component T (f.hom.thickening.appTop a) = F.val.map f.op (component U a)
  /-- Each component satisfies the Leibniz rule over its ring of sections. -/
  leibniz : ∀ (T : smallCrystallineSite B.scheme B.ideal B.dividedPowers
      B.compatible B.source B.sourceToClosed)
      (a b : (smallStructureSheaf (S := B.scheme) (I := B.ideal)
        (γ := B.dividedPowers) (h_compatible := B.compatible)
        (X := B.source) (x₀ := B.sourceToClosed)).obj.obj (op T)),
    component T (a * b) = a • component T b + b • component T a
  /-- Sections pulled back from every base open through which the thickening factors vanish. -/
  base_vanish : ∀ (T : smallCrystallineSite B.scheme B.ideal B.dividedPowers
      B.compatible B.source B.sourceToClosed) (V : B.scheme.Opens)
      (h : ⊤ ≤ T.obj.1.thickeningToBase ⁻¹ᵁ V) (a : Γ(B.scheme, V)),
    component T (T.obj.1.thickeningToBase.appLE V ⊤ h a) = 0
  /-- Divided powers satisfy the derivation identity on each actual affine open restriction. -/
  dividedPower : ∀ (T : smallCrystallineSite B.scheme B.ideal B.dividedPowers
      B.compatible B.source B.sourceToClosed) (W : T.obj.1.thickening.affineOpens)
      (n : ℕ+) (x : Γ(T.obj.1.thickening, W)), x ∈ T.obj.1.ideal.ideal W →
    let R := (smallStructureSheaf (S := B.scheme) (I := B.ideal)
      (γ := B.dividedPowers) (h_compatible := B.compatible)
      (X := B.source) (x₀ := B.sourceToClosed)).obj.obj
        (op ((smallOpensFunctor T).obj W.1))
    let restriction : Γ(T.obj.1.thickening, W) →+* R :=
      (W.1.ι.appLE W.1 ⊤ (fun y _ => y.property)).hom
    let D := component ((smallOpensFunctor T).obj W.1)
    D (restriction ((T.obj.1.gamma W).dpow (n : ℕ) x)) =
      restriction ((T.obj.1.gamma W).dpow ((n : ℕ) - 1) x) • D (restriction x)

/-- Construct a small crystalline `S`-derivation from additive maps and their
naturality, Leibniz, base-vanishing, and divided-power laws. -/
def SDerivation.of
    (component : ∀ T : smallCrystallineSite B.scheme B.ideal B.dividedPowers
        B.compatible B.source B.sourceToClosed,
      Γ(T.obj.1.thickening, ⊤) →+ F.val.obj (op T))
    (natural : ∀ {T U : smallCrystallineSite B.scheme B.ideal B.dividedPowers
        B.compatible B.source B.sourceToClosed} (f : T ⟶ U)
        (a : Γ(U.obj.1.thickening, ⊤)),
      component T (f.hom.thickening.appTop a) = F.val.map f.op (component U a))
    (leibniz : ∀ (T : smallCrystallineSite B.scheme B.ideal B.dividedPowers
        B.compatible B.source B.sourceToClosed)
        (a b : (smallStructureSheaf (S := B.scheme) (I := B.ideal)
          (γ := B.dividedPowers) (h_compatible := B.compatible)
          (X := B.source) (x₀ := B.sourceToClosed)).obj.obj (op T)),
      component T (a * b) = a • component T b + b • component T a)
    (base_vanish : ∀ (T : smallCrystallineSite B.scheme B.ideal B.dividedPowers
        B.compatible B.source B.sourceToClosed) (V : B.scheme.Opens)
        (h : ⊤ ≤ T.obj.1.thickeningToBase ⁻¹ᵁ V) (a : Γ(B.scheme, V)),
      component T (T.obj.1.thickeningToBase.appLE V ⊤ h a) = 0)
    (dividedPower : ∀ (T : smallCrystallineSite B.scheme B.ideal B.dividedPowers
        B.compatible B.source B.sourceToClosed) (W : T.obj.1.thickening.affineOpens)
        (n : ℕ+) (x : Γ(T.obj.1.thickening, W)), x ∈ T.obj.1.ideal.ideal W →
      let R := (smallStructureSheaf (S := B.scheme) (I := B.ideal)
        (γ := B.dividedPowers) (h_compatible := B.compatible)
        (X := B.source) (x₀ := B.sourceToClosed)).obj.obj
          (op ((smallOpensFunctor T).obj W.1))
      let restriction : Γ(T.obj.1.thickening, W) →+* R :=
        (W.1.ι.appLE W.1 ⊤ (fun y _ => y.property)).hom
      let D := component ((smallOpensFunctor T).obj W.1)
      D (restriction ((T.obj.1.gamma W).dpow (n : ℕ) x)) =
        restriction ((T.obj.1.gamma W).dpow ((n : ℕ) - 1) x) • D (restriction x)) :
    SDerivation B F :=
  { component, natural, leibniz, base_vanish, dividedPower }

/-- A small crystalline `S`-derivation satisfies naturality, the Leibniz rule,
vanishing on every factoring base open, and affine-local divided-power compatibility. -/
theorem SDerivation.spec (D : SDerivation B F) :
    (∀ {T U : smallCrystallineSite B.scheme B.ideal B.dividedPowers
        B.compatible B.source B.sourceToClosed} (f : T ⟶ U)
        (a : Γ(U.obj.1.thickening, ⊤)),
      D.component T (f.hom.thickening.appTop a) = F.val.map f.op (D.component U a)) ∧
    (∀ (T : smallCrystallineSite B.scheme B.ideal B.dividedPowers
        B.compatible B.source B.sourceToClosed)
        (a b : (smallStructureSheaf (S := B.scheme) (I := B.ideal)
          (γ := B.dividedPowers) (h_compatible := B.compatible)
          (X := B.source) (x₀ := B.sourceToClosed)).obj.obj (op T)),
      D.component T (a * b) = a • D.component T b + b • D.component T a) ∧
    (∀ (T : smallCrystallineSite B.scheme B.ideal B.dividedPowers
        B.compatible B.source B.sourceToClosed) (V : B.scheme.Opens)
        (h : ⊤ ≤ T.obj.1.thickeningToBase ⁻¹ᵁ V) (a : Γ(B.scheme, V)),
      D.component T (T.obj.1.thickeningToBase.appLE V ⊤ h a) = 0) ∧
    (∀ (T : smallCrystallineSite B.scheme B.ideal B.dividedPowers
        B.compatible B.source B.sourceToClosed) (W : T.obj.1.thickening.affineOpens)
        (n : ℕ+) (x : Γ(T.obj.1.thickening, W)), x ∈ T.obj.1.ideal.ideal W →
      let R := (smallStructureSheaf (S := B.scheme) (I := B.ideal)
        (γ := B.dividedPowers) (h_compatible := B.compatible)
        (X := B.source) (x₀ := B.sourceToClosed)).obj.obj
          (op ((smallOpensFunctor T).obj W.1))
      let restriction : Γ(T.obj.1.thickening, W) →+* R :=
        (W.1.ι.appLE W.1 ⊤ (fun y _ => y.property)).hom
      let d := D.component ((smallOpensFunctor T).obj W.1)
      d (restriction ((T.obj.1.gamma W).dpow (n : ℕ) x)) =
        restriction ((T.obj.1.gamma W).dpow ((n : ℕ) - 1) x) • d (restriction x)) := sorry

end AlgebraicGeometry.Scheme.Crystalline
