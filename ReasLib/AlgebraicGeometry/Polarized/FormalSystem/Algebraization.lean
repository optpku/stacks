module

public import ReasLib.AlgebraicGeometry.Polarized.FormalSystem

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- A sequential polarized formal system admits a proper flat finitely
presented algebraization with an ample invertible module and compatible stage
and line-module identifications. -/
theorem strongFormalEffectiveness (ξ : FormalSystem.{u}) :
    ∃ (X : Scheme.{u}) (f : X ⟶ ξ.limitSpec) (L : X.Modules)
      (hf_proper : IsProper f) (hf_flat : Flat f)
      (hf_fp : Scheme.Hom.FinitePresentation f)
      (hL_inv : Scheme.Modules.Invertible L)
      (hL_ample : @Scheme.Modules.IsAmple X L hL_inv)
      (cX : ∀ n, ξ.X n ⟶ X)
      (hcX_pullback : ∀ n, IsPullback (cX n) (ξ.hom n) f (ξ.stageToLimit n))
      (cL : ∀ n, (Scheme.Modules.pullback (cX n)).obj L ≅ ξ.line n)
      (hcX_comp : ∀ n, cX n = ξ.step n ≫ cX (n + 1)),
      ∀ n,
        cL n =
          (Scheme.Modules.pullbackCongr (hcX_comp n)).app L ≪≫
            (Scheme.Modules.pullbackComp (ξ.step n) (cX (n + 1))).symm.app L ≪≫
              (Scheme.Modules.pullback (ξ.step n)).mapIso (cL (n + 1)) ≪≫
                ξ.iso n := sorry

end AlgebraicGeometry.Polarized
