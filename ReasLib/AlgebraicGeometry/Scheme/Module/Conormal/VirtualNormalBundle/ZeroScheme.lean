/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.VirtualNormalBundle.IdealSurjection
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Dual
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit

/-!
# Virtual normal bundles of zero schemes

A section of an invertible module determines a canonical rank-one virtual normal bundle
on its zero scheme, with underlying module the pullback of the invertible module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

/-- The canonical surjection from the dual of the pulled-back invertible module onto the
pulled-back kernel ideal of a zero-scheme immersion. -/
noncomputable def zeroSchemeIdealSurjection
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) :
    Scheme.Modules.dual ((Scheme.Modules.pullback (zeroSchemeι ℒ s)).obj ℒ) ⟶
      (Scheme.Modules.pullback (zeroSchemeι ℒ s)).obj
        (RingedSpace.Hom.kernelIdealSheaf (zeroSchemeι ℒ s).toShHom) :=
  (Scheme.Modules.pullbackDualIso (zeroSchemeι ℒ s) ℒ
      (@Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
        _ 1 ℒ (Scheme.Modules.isFiniteLocallyFreeOfRankOne_of_invertible ℒ))).inv ≫
    (Scheme.Modules.pullback (zeroSchemeι ℒ s)).map
      ((ihom ℒ).map (RingedSpace.unitIsoTensorUnit X.toRingedSpace).inv ≫
        factorThruImageSubobject (dualSectionHom ℒ s) ≫
          eqToHom
            (congrArg (fun I : X.IdealSubobject ↦ I.toModule)
              (zeroIdealSheaf_toSubobject ℒ s).symm) ≫
          (zeroIdealSheaf ℒ s).toModuleIso.hom)

/-- The canonical dual-to-ideal map for a zero scheme is an epimorphism. -/
instance zeroSchemeIdealSurjection_epi
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) : Epi (zeroSchemeIdealSurjection ℒ s) := sorry

/-- The zero-scheme immersion of a section of an invertible module is a closed immersion. -/
instance zeroSchemeι_isClosedImmersion
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) : IsClosedImmersion (zeroSchemeι ℒ s) :=
  inferInstanceAs (IsClosedImmersion (zeroIdealSheaf ℒ s).subschemeι)

/-- The zero scheme of a section of an invertible module has a canonical virtual normal
bundle whose module is the pullback of that invertible module. -/
noncomputable def ofZeroScheme
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) :
    VirtualNormalBundle (zeroSchemeι ℒ s) :=
  ofIdealSurjection (zeroSchemeι ℒ s)
    ((Scheme.Modules.pullback (zeroSchemeι ℒ s)).obj ℒ)
    (zeroSchemeIdealSurjection ℒ s)

/-- The module of the canonical zero-scheme virtual normal bundle is the pullback of the
invertible module. -/
theorem ofZeroScheme_module
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) :
    (ofZeroScheme ℒ s).module =
      (Scheme.Modules.pullback (zeroSchemeι ℒ s)).obj ℒ := sorry

/-- The quotient map of the canonical zero-scheme virtual normal bundle is the
dual-to-ideal surjection followed by the conormal comparison. -/
theorem ofZeroScheme_map
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) :
    (ofZeroScheme ℒ s).map =
      zeroSchemeIdealSurjection ℒ s ≫
        Conormal.pullbackIdealComparison (zeroSchemeι ℒ s) := sorry

/-- The canonical virtual normal bundle of a zero scheme is finite locally free and has
an epimorphic dual-to-conormal map. -/
theorem ofZeroScheme_spec
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) :
    Scheme.Modules.IsFiniteLocallyFree (ofZeroScheme ℒ s).module ∧
      Epi (ofZeroScheme ℒ s).map := sorry

/-- The module of the canonical zero-scheme virtual normal bundle has rank one. -/
theorem ofZeroScheme_module_isFiniteLocallyFreeOfRank
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank 1 (ofZeroScheme ℒ s).module := sorry

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
