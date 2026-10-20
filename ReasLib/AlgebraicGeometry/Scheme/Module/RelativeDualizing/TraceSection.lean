/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.TraceElement
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf

variable {X Y : Scheme.{u}} {f : Y ⟶ X}
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
variable [LocallyOfFiniteType f] [LocallyQuasiFinite f] [Flat f]

/-- A global section of a relative dualizing sheaf is a trace section when its image in
every chosen affine finite/open model is a ring-level universal trace element. -/
def IsTraceSection (W : f.RelativeDualizingSheaf)
    (τ : W.module.obj.sections) : Prop :=
  ∀ (U : X.affineOpens) (V : Y.affineOpens) (hVU : V ≤ f ⁻¹ᵁ U),
    let P := W.presentation U V hVU
    @Algebra.RelativeDualizingModule.TraceElement.IsUniversal
      Γ(X, U) P.finiteModel Γ(Y, V) _ _ _
      (IsLocallyNoetherian.component_noetherian U)
      (IsLocallyNoetherian.component_noetherian V)
      P.toFinite.hom.toAlgebra P.toTarget.hom.toAlgebra
      (f.appLE U V hVU).hom.toAlgebra P.isScalarTower
      (Flat.flat_appLE f U.2 V.2 hVU)
      (f.affineQuasiFinite U V hVU) P.finite P.openImmersion
      ((W.sectionIso U V hVU).hom (τ.1 (Opposite.op V.1)))

/-- A trace section is characterized by the ring-level universality condition on every
compatible chosen affine model. -/
theorem isTraceSection_iff (W : f.RelativeDualizingSheaf)
    (τ : W.module.obj.sections) :
    W.IsTraceSection τ ↔
      ∀ (U : X.affineOpens) (V : Y.affineOpens) (hVU : V ≤ f ⁻¹ᵁ U),
        let P := W.presentation U V hVU
        @Algebra.RelativeDualizingModule.TraceElement.IsUniversal
          Γ(X, U) P.finiteModel Γ(Y, V) _ _ _
          (IsLocallyNoetherian.component_noetherian U)
          (IsLocallyNoetherian.component_noetherian V)
          P.toFinite.hom.toAlgebra P.toTarget.hom.toAlgebra
          (f.appLE U V hVU).hom.toAlgebra P.isScalarTower
          (Flat.flat_appLE f U.2 V.2 hVU)
          (f.affineQuasiFinite U V hVU) P.finite P.openImmersion
          ((W.sectionIso U V hVU).hom (τ.1 (Opposite.op V.1))) :=
  Iff.rfl

/-- Two trace sections of the same relative dualizing sheaf are equal. -/
theorem IsTraceSection.eq (W : f.RelativeDualizingSheaf)
    {τ₁ τ₂ : W.module.obj.sections} (hτ₁ : W.IsTraceSection τ₁)
    (hτ₂ : W.IsTraceSection τ₂) : τ₁ = τ₂ := sorry

/-- A relative dualizing sheaf of a flat locally quasi-finite morphism of locally
Noetherian schemes admits a global trace section. -/
theorem exists_traceSection {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [Flat f]
    (W : f.RelativeDualizingSheaf) :
    ∃ τ : W.module.obj.sections, W.IsTraceSection τ := sorry

end AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf
