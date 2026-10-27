/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Differentials

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Crystalline
open KaehlerDifferential.DeRham
open scoped AlgebraicGeometry RelativeDerivation

universe u

/-- On an affine small crystalline object mapping into an affine base open, sections of
the universal crystalline differential sheaf are uniquely linearly equivalent to the
ring-level divided-power differential module, compatibly with the universal derivations. -/
theorem CrystallineDifferentials.existsUnique_affineSectionsLinearEquiv
    {p : ℕ} [Fact (Nat.Prime p)]
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {h_I_quasiCoherent : I.toModule.IsQuasicoherent}
    {s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    {h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))}
    (Ω : CrystallineDifferentials p S I γ h_compatible h_I_quasiCoherent s X x₀ h_p)
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    [IsAffine T.obj.1.thickening]
    (V : S.affineOpens)
    (hTV : (⊤ : T.obj.1.thickening.Opens) ≤ T.obj.1.thickeningToBase ⁻¹ᵁ V.1) :
    let W : T.obj.1.thickening.affineOpens := ⟨⊤, isAffineOpen_top T.obj.1.thickening⟩
    ∃! eΩ : Γ(Ω.module.obj T.obj.1, ⊤) ≃ₗ[Γ(T.obj.1.thickening, ⊤)]
      dividedPowerDifferential
        (T.obj.1.thickeningToBase.appLE V.1 W.1 hTV).hom (T.obj.1.gamma W),
      ∀ a : Γ(T.obj.1.thickening, ⊤),
        eΩ (((Ω.derivation.component T.obj.1).app (op ⊤)).d a) =
          dividedPowerDifferentialDerivation
            (T.obj.1.thickeningToBase.appLE V.1 W.1 hTV).hom (T.obj.1.gamma W) a := sorry

end
