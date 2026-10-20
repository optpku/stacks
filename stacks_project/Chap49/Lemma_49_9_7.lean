/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different.Norm
import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.TraceSection
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory SheafOfModules
open scoped AlgebraicGeometry

universe u

/- Lemma 49.9.7 (1): if the relative dualizing sheaf is invertible, then the
different is a locally principal closed subscheme. -/
@[stacks 0BWA] #check (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.different_isLocallyPrincipalClosedSubscheme :
    ∀ {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
      [Flat f] [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf)
      (τ : sections W.module.obj)
      (hτ : W.IsTraceSection τ)
      [Scheme.Modules.Invertible W.module.obj],
      IsLocallyPrincipalClosedSubscheme (W.different τ).subschemeι)

/- Lemma 49.9.7 (2): for a finite morphism, locally a generator of the different has norm
generating the same ideal as the discriminant of a basis. -/
@[stacks 0BWA]
#check (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.normDifferent_eq_discriminant :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsNoetherian X] [IsNoetherian Y]
      [IsFinite f] [Flat f] [Scheme.Hom.QuasiFinite f]
      (W : f.RelativeDualizingSheaf) (τ : sections W.module.obj)
      (hτ : W.IsTraceSection τ)
      [Scheme.Modules.Invertible W.module.obj]
      (N : Scheme.FiniteMorphismNorm f) (hN : N.IsDeterminant),
      ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ n : ℕ, ∃ e : Module.Basis (Fin n) Γ(X, U) Γ(Y, f ⁻¹ᵁ U),
          ∃ b : Γ(Y, f ⁻¹ᵁ U),
            (W.different τ).ideal ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ = Ideal.span {b} ∧
              Ideal.span {N.app U b} = Ideal.span {Algebra.discr Γ(X, U) e})

/- Lemma 49.9.7 (3): if the morphism is étale at every associated point of the
source, then the different is an effective Cartier divisor. -/
@[stacks 0BWA]
#check (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.different_isEffectiveCartierDivisor :
    ∀ {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
      [Flat f] [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf)
      (τ : sections W.module.obj)
      (hτ : W.IsTraceSection τ)
      [Scheme.Modules.Invertible W.module.obj]
      (h_assoc : ∀ y : Y, y ∈ Y.associatedPoints → f.EtaleAt y),
      IsEffectiveCartierDivisor (W.different τ).subschemeι)

/- Lemma 49.9.7 (4): if the morphism is étale at every associated point of the
source, then the different is an effective Cartier divisor whose associated sheaf
is isomorphic to the relative dualizing sheaf. -/
@[stacks 0BWA]
#check (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.nonempty_differentAssociatedSheafIso :
    ∀ {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
      [Flat f] [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf)
      (τ : sections W.module.obj)
      (hτ : W.IsTraceSection τ)
      [Scheme.Modules.Invertible W.module.obj]
      (h_assoc : ∀ y : Y, y ∈ Y.associatedPoints → f.EtaleAt y),
      ∃ hD : IsEffectiveCartierDivisor (W.different τ).subschemeι,
        Nonempty (@AlgebraicGeometry.Scheme.IdealSheafData.associatedSheaf Y
          (W.different τ) hD ≅ W.module.obj))

/- Lemma 49.9.7 (5): for an effective Cartier different, the section-preserving
comparison with the relative dualizing sheaf is unique. -/
@[stacks 0BWA]
#check (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.existsUnique_differentAssociatedSheafIso :
    ∀ {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
      [Flat f] [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf)
      (τ : sections W.module.obj)
      (hτ : W.IsTraceSection τ)
      [Scheme.Modules.Invertible W.module.obj]
      [IsEffectiveCartierDivisor (W.different τ).subschemeι],
      ∃! e : (W.different τ).associatedSheaf ≅ W.module.obj,
        SheafOfModules.sectionsMap e.hom (W.different τ).canonicalSection = τ)
