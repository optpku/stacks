/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different.Support
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ZeroScheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.RegularSection

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory SheafOfModules
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Hom
namespace RelativeDualizingSheaf

/-- The different ideal sheaf of an invertible relative dualizing sheaf is the zero ideal sheaf of its trace section. -/
theorem different_eq_zeroIdealSheaf
    {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
    [Flat f] [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf)
    (τ : sections W.module.obj) [Scheme.Modules.Invertible W.module.obj] :
    W.different τ = Scheme.zeroIdealSheaf W.module.obj τ := sorry

/-- The different of an invertible relative dualizing sheaf is a locally principal closed subscheme. -/
theorem different_isLocallyPrincipalClosedSubscheme
    {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
    [Flat f] [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf)
    (τ : sections W.module.obj)
    (hτ : AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.IsTraceSection W τ)
    [Scheme.Modules.Invertible W.module.obj] :
    IsLocallyPrincipalClosedSubscheme
      (W.different τ).subschemeι := sorry

/-- If the morphism is étale at every associated point of the source, the different is an effective Cartier divisor. -/
theorem different_isEffectiveCartierDivisor
    {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
    [Flat f] [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf)
    (τ : sections W.module.obj)
    (hτ : AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.IsTraceSection W τ)
    [Scheme.Modules.Invertible W.module.obj]
    (h_assoc : ∀ y : Y, y ∈ Y.associatedPoints → f.EtaleAt y) :
    IsEffectiveCartierDivisor
      (W.different τ).subschemeι := sorry

/-- Under associated-point étaleness, the different's associated sheaf is isomorphic to the relative dualizing sheaf. -/
theorem nonempty_differentAssociatedSheafIso
    {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
    [Flat f] [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf)
    (τ : sections W.module.obj)
    (hτ : AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.IsTraceSection W τ)
    [Scheme.Modules.Invertible W.module.obj]
    (h_assoc : ∀ y : Y, y ∈ Y.associatedPoints → f.EtaleAt y) :
    ∃ hD : IsEffectiveCartierDivisor
        (W.different τ).subschemeι,
      Nonempty
        (@IdealSheafData.associatedSheaf Y
          (W.different τ) hD ≅ W.module.obj) := sorry

/-- For an effective Cartier different, the section-preserving comparison with the relative dualizing sheaf is unique. -/
theorem existsUnique_differentAssociatedSheafIso
    {X Y : Scheme.{u}} {f : Y ⟶ X} [IsNoetherian X] [IsNoetherian Y]
    [Flat f] [Scheme.Hom.QuasiFinite f] (W : f.RelativeDualizingSheaf)
    (τ : sections W.module.obj)
    (hτ : AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf.IsTraceSection W τ)
    [Scheme.Modules.Invertible W.module.obj]
    [IsEffectiveCartierDivisor
      (W.different τ).subschemeι] :
    ∃! e : (W.different τ).associatedSheaf ≅ W.module.obj,
      SheafOfModules.sectionsMap e.hom
        (W.different τ).canonicalSection = τ := sorry

end RelativeDualizingSheaf
end Hom
end Scheme
end AlgebraicGeometry
