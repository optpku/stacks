/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Remark_60_24_10_Rlim_Stage
public import stacks_project.Chap60.Remark_60_24_10_Rlim_Restriction
public import stacks_project.Chap60.Remark_60_24_10_Rlim_System
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Crystalline

universe u v w

@[expose] public section

/-- Remark 60.24.10 (Rlim): in the affine divided-power setup of Situation 60.7.5, for any
`O_{X/S}`-module `F` and `e₀` large enough that `(p^e) ⊂ I` is `γ`-stable for `e ≥ e₀`,
`RΓ(Cris(X/S), F)` is the derived inverse limit of `RΓ(Cris(X/S_e), F_e)` on the
`p`-power stages `S_e = Spec(A / ⟨p^e⟩)`. -/
@[stacks 07MV]
theorem crystallineCohomologyRlim
    (p : ℕ) [Fact (Nat.Prime p)]
    (A : Type u) [CommRing A] [Algebra (Int.LocalizationAtPrime p) A]
    (I : (Spec (.of A)).IdealSheafData)
    (γ : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : (Spec (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
        (γ V).IsDPMorphism (γ ((Spec (.of A)).affineBasicOpen f))
          ((Spec (.of A)).presheaf.map
            (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_pAmodI :
      IsNilpotent
        (Ideal.Quotient.mk
          (I.ideal ⟨⊤, isAffineOpen_top (Spec (.of A))⟩)
          (p : Γ(Spec (.of A), ⊤))))
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (F : CrystallineModuleSheaf (Spec (.of A)) I γ h_compatible X x₀)
    {D : Type w} [Category.{v, w} D] [Preadditive D]
    [Limits.HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (e₀ : ℕ)
    (h_tail :
      ∀ (e : ℕ), e₀ ≤ e → ∀ V : (Spec (.of A)).affineOpens,
        Ideal.span {((p : Γ(Spec (.of A), V)) ^ e)} ≤ I.ideal V ∧
          ∀ (n : ℕ) (x : Γ(Spec (.of A), V)),
            x ∈ Ideal.span {((p : Γ(Spec (.of A), V)) ^ e)} →
              (γ V).dpow n x ∈ Ideal.span {((p : Γ(Spec (.of A), V)) ^ e)})
    (rGamma :
      CrystallineModuleSheaf (Spec (.of A)) I γ h_compatible X x₀ → D)
    (rGammaStage :
      ∀ e : ℕ, PPowerStageModuleSheaf p I γ h_compatible X x₀ e → D)
    (rGammaStageRestrict :
      ∀ (e : ℕ) (F_e : PPowerStageModuleSheaf p I γ h_compatible X x₀ e),
        rGammaStage (e + 1) (restrictPPowerStageSucc p F_e) ⟶ rGammaStage e F_e) :
    HomotopyLimit.IsOf
      (pPowerStageRGammaSystem p rGammaStage rGammaStageRestrict F e₀)
      (rGamma F) := sorry
