/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing.Different
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf

variable {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'}
variable [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
variable [Flat f] [Scheme.Hom.QuasiFinite f]
variable [Flat f'] [Scheme.Hom.QuasiFinite f']

/-- The morphism from the different after base change to the pullback of the original
different, induced by an inclusion of their ideal sheaves. -/
noncomputable def baseChangeComparison (W : f.RelativeDualizingSheaf)
    (W' : f'.RelativeDualizingSheaf) (h : Y' ⟶ Y)
    (τ : W.module.obj.sections) (τ' : W'.module.obj.sections)
    (hle : (W.different τ).comap h ≤ W'.different τ') :
    (W'.different τ').subscheme ⟶ pullback h (W.different τ).subschemeι :=
  Scheme.IdealSheafData.inclusion hle ≫ ((W.different τ).comapIso h).hom

/-- The comparison followed by the projection to the base-changed source is the closed
subscheme inclusion of the base-changed different. -/
theorem baseChangeComparison_fst (W : f.RelativeDualizingSheaf)
    (W' : f'.RelativeDualizingSheaf) (h : Y' ⟶ Y)
    (τ : W.module.obj.sections) (τ' : W'.module.obj.sections)
    (hle : (W.different τ).comap h ≤ W'.different τ') :
    W.baseChangeComparison W' h τ τ' hle ≫
        pullback.fst h (W.different τ).subschemeι =
      (W'.different τ').subschemeι := sorry

/-- The comparison followed by the projection to the original different is its canonical
subscheme map along the base-change morphism. -/
theorem baseChangeComparison_snd (W : f.RelativeDualizingSheaf)
    (W' : f'.RelativeDualizingSheaf) (h : Y' ⟶ Y)
    (τ : W.module.obj.sections) (τ' : W'.module.obj.sections)
    (hle : (W.different τ).comap h ≤ W'.different τ') :
    W.baseChangeComparison W' h τ τ' hle ≫
        pullback.snd h (W.different τ).subschemeι =
      (W'.different τ').subschemeMap (W.different τ) h
        (Scheme.IdealSheafData.le_map_iff_comap_le.mpr hle) := sorry

/-- The cartesian base-change square carries the pullback of the different ideal sheaf into
the different ideal sheaf of the base-changed morphism. -/
theorem comap_le_of_isPullback (W : f.RelativeDualizingSheaf)
    (W' : f'.RelativeDualizingSheaf) (g : X' ⟶ X) (h : Y' ⟶ Y)
    (τ : W.module.obj.sections) (τ' : W'.module.obj.sections)
    (sq : IsPullback h f' f g) (hτ : W.IsTraceSection τ)
    (hτ' : W'.IsTraceSection τ') :
    (W.different τ).comap h ≤ W'.different τ' := sorry

/-- In a cartesian square of Noetherian schemes, the map from the different of a flat
quasi-finite morphism after base change to the pullback of its different is a closed
immersion. -/
theorem baseChangeComparison_isClosedImmersion (W : f.RelativeDualizingSheaf)
    (W' : f'.RelativeDualizingSheaf) (g : X' ⟶ X) (h : Y' ⟶ Y)
    (τ : W.module.obj.sections) (τ' : W'.module.obj.sections)
    (sq : IsPullback h f' f g) (hτ : W.IsTraceSection τ)
    (hτ' : W'.IsTraceSection τ') :
    IsClosedImmersion
      (W.baseChangeComparison W' h τ τ'
        (comap_le_of_isPullback W W' g h τ τ' sq hτ hτ')) := sorry

/-- The closed immersion from the base-changed different to the pullback of the original
different is bijective on underlying points. -/
theorem baseChange_bijective (W : f.RelativeDualizingSheaf)
    (W' : f'.RelativeDualizingSheaf) (g : X' ⟶ X) (h : Y' ⟶ Y)
    (τ : W.module.obj.sections) (τ' : W'.module.obj.sections)
    (sq : IsPullback h f' f g) (hτ : W.IsTraceSection τ)
    (hτ' : W'.IsTraceSection τ') :
    Function.Bijective ⇑(ConcreteCategory.hom
      (W.baseChangeComparison W' h τ τ'
        (comap_le_of_isPullback W W' g h τ τ' sq hτ hτ')).base) := sorry

/-- If the base morphism is flat or the relative dualizing sheaf is invertible, then
formation of the different commutes with the cartesian base change. -/
theorem baseChange_eq_of_flat_or_isInvertible (W : f.RelativeDualizingSheaf)
    (W' : f'.RelativeDualizingSheaf) (g : X' ⟶ X) (h : Y' ⟶ Y)
    (τ : W.module.obj.sections) (τ' : W'.module.obj.sections)
    (sq : IsPullback h f' f g) (hτ : W.IsTraceSection τ)
    (hτ' : W'.IsTraceSection τ') :
    Flat g ∨ Scheme.Modules.Invertible W.module.obj →
      W'.different τ' = (W.different τ).comap h := sorry

/-- Under flat base change or invertibility of the relative dualizing sheaf, the canonical
comparison of different closed subschemes is an isomorphism. -/
theorem baseChangeComparison_isIso (W : f.RelativeDualizingSheaf)
    (W' : f'.RelativeDualizingSheaf) (g : X' ⟶ X) (h : Y' ⟶ Y)
    (τ : W.module.obj.sections) (τ' : W'.module.obj.sections)
    (sq : IsPullback h f' f g) (hτ : W.IsTraceSection τ)
    (hτ' : W'.IsTraceSection τ') :
    Flat g ∨ Scheme.Modules.Invertible W.module.obj →
      IsIso (W.baseChangeComparison W' h τ τ'
        (comap_le_of_isPullback W W' g h τ τ' sq hτ hτ')) := sorry

end AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf
