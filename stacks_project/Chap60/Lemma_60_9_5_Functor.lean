/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.OpenRestriction

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

universe u

noncomputable section

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S S' X X' : Scheme.{u}}
variable (iX : X' ⟶ X) [IsOpenImmersion iX]

variable (I : S.IdealSheafData) (I' : S'.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (γ' : ∀ V : S'.affineOpens, DividedPowers (I'.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (g : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
      (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom)
variable (h'_compatible :
  ∀ (V : S'.affineOpens) (g : Γ(S', V)),
    (γ' V).IsDPMorphism (γ' (S'.affineBasicOpen g))
      (S'.presheaf.map (homOfLE (S'.basicOpen_le g)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (x₀ : X ⟶ I.subscheme) (x₀' : X' ⟶ I'.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (h_p' : ∀ U : X'.affineOpens, IsNilpotent (p : Γ(X', U)))

/- The divided-power morphism induced by the open base inclusion. -/
variable (g : DividedPowerSchemeHom I' I s' s)
variable (h_comm : iX ≫ x₀ = x₀' ≫ g.zeroFiberMap)
variable (h_dividedPowers :
  ∀ (V : S.affineOpens) (W : S'.affineOpens)
    (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
    (γ V).IsDPMorphism (γ' W) (g.base.appLE V W hVW).hom)

/-- The concrete open-restriction functor between the two small crystalline sites. -/
abbrev openCrystallineSmallFunctor :
    Scheme.Crystalline.smallCrystallineSite S' I' γ' h'_compatible X' x₀' ⥤
      Scheme.Crystalline.smallCrystallineSite S I γ h_compatible X x₀ :=
  Scheme.Crystalline.openRestrictionFunctor iX I I' γ γ' h_compatible h'_compatible
    s s' x₀ x₀' h_p h_p' g.base g.zeroFiberMap g.zeroFiber_comm g.base_over
    g.ideal_compatible h_comm h_dividedPowers

end
