/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different.Gorenstein
import StacksCheckRecall

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme
  AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf CategoryTheory
  CategoryTheory.Limits SheafOfModules
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf

/- Remark 49.16.2 (1) -/
@[stacks 0C17] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.different_locallyPrincipalIdeal_of_gorenstein :
    ∀ {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
      [Scheme.Hom.QuasiFinite f] [AlgebraicGeometry.Gorenstein f]
      (W : f.RelativeDualizingSheaf) (τ : sections W.module.obj)
      (hτ : W.IsTraceSection τ),
      ∀ y : Y, ∃ V : Y.affineOpens, y ∈ (V : Y.Opens) ∧
        ∃ b : Γ(Y, V),
          (W.different τ).ideal V = Ideal.span ({b} : Set Γ(Y, V)))

/- Remark 49.16.2 (2) -/
@[stacks 0C17] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.different_locallyPrincipalClosedSubscheme_of_gorenstein :
    ∀ {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
      [Scheme.Hom.QuasiFinite f] [AlgebraicGeometry.Gorenstein f]
      (W : f.RelativeDualizingSheaf) (τ : sections W.module.obj)
      (hτ : W.IsTraceSection τ),
      IsLocallyPrincipalClosedSubscheme (W.different τ).subschemeι)

/- Remark 49.16.2 (3) -/
@[stacks 0C17] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.different_eq_noetherDifferent_on_affine_of_gorenstein :
    ∀ {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
      [Scheme.Hom.QuasiFinite f] [AlgebraicGeometry.Gorenstein f]
      (W : f.RelativeDualizingSheaf) (τ : sections W.module.obj)
      (hτ : W.IsTraceSection τ) (U : X.affineOpens) (V : Y.affineOpens)
      (hVU : V ≤ f ⁻¹ᵁ U),
      (W.different τ).ideal V =
        KaehlerDifferential.noetherDifferent Γ(X, U)
          (f.sectionsAlg (U : X.Opens) (V : Y.Opens) hVU))

/- Remark 49.16.2 (4) -/
@[stacks 0C17] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.different_baseChange_of_gorenstein :
    ∀ {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'}
      [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
      [Scheme.Hom.QuasiFinite f] [AlgebraicGeometry.Gorenstein f]
      [Flat f'] [Scheme.Hom.QuasiFinite f']
      (W : f.RelativeDualizingSheaf) (W' : f'.RelativeDualizingSheaf)
      (g : X' ⟶ X) (h : Y' ⟶ Y)
      (τ : sections W.module.obj) (τ' : sections W'.module.obj)
      (sq : IsPullback h f' f g) (hτ : W.IsTraceSection τ)
      (hτ' : W'.IsTraceSection τ'),
      W'.different τ' = (W.different τ).comap h)

/- Remark 49.16.2 (5) -/
@[stacks 0C17] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.normDifferent_eq_discriminant_of_gorenstein :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsNoetherian X] [IsNoetherian Y]
      [IsFinite f] [Scheme.Hom.QuasiFinite f] [AlgebraicGeometry.Gorenstein f]
      (W : f.RelativeDualizingSheaf) (τ : sections W.module.obj)
      (hτ : W.IsTraceSection τ),
      ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ n : ℕ,
          ∃ e : Module.Basis (Fin n) Γ(X, U)
            (f.sectionsAlg (U : X.Opens) (f ⁻¹ᵁ U) le_rfl),
            ∃ b : f.sectionsAlg (U : X.Opens) (f ⁻¹ᵁ U) le_rfl,
              (W.different τ).ideal ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ = Ideal.span {b} ∧
                Ideal.span {Algebra.norm Γ(X, U) b} =
                  Ideal.span {Algebra.discr Γ(X, U) e})

/- Remark 49.16.2 (6) -/
@[stacks 0C17] #check
  (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.different_cartierAssociatedSheaf_of_gorenstein :
    ∀ {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
      [Scheme.Hom.QuasiFinite f] [AlgebraicGeometry.Gorenstein f]
      (W : f.RelativeDualizingSheaf) (τ : sections W.module.obj)
      (hτ : W.IsTraceSection τ)
      (h_assoc : ∀ y : Y, y ∈ Y.associatedPoints → f.EtaleAt y),
      ∃ hD : IsEffectiveCartierDivisor (W.different τ).subschemeι,
        Nonempty ((W.different τ).associatedSheaf (hD := hD) ≅ W.module.obj))

end RelativeDualizingSheaf
end Hom
end Scheme
end AlgebraicGeometry
