module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.VirtualNormalBundle.IdealSurjection
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Dual
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit

/-!
# Virtual normal bundle of a zero-scheme triple

A global section of an invertible module determines a canonical rank-one virtual normal
bundle on its zero scheme, with underlying module the pullback of the invertible sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle

/-- The dual of a module sheaf compared with internal Hom into the structure module. -/
noncomputable def dualIhomUnitHom {X : Scheme.{u}} (ℒ : X.Modules) :
    Scheme.Modules.dual ℒ ⟶
      (ihom ℒ).obj (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  (ihom ℒ).map (RingedSpace.unitIsoTensorUnit X.toRingedSpace).inv

/-- `dualIhomUnitHom` is internal Hom applied to the tensor-unit comparison. -/
theorem dualIhomUnitHom_def {X : Scheme.{u}} (ℒ : X.Modules) :
    dualIhomUnitHom ℒ =
      (ihom ℒ).map (RingedSpace.unitIsoTensorUnit X.toRingedSpace).inv := sorry

/-- Dual-section evaluation, factored through the zero-ideal image and identified with the
kernel ideal of the zero-scheme immersion. -/
noncomputable def dualSectionToKernelIdeal
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) :
    Scheme.Modules.dual ℒ ⟶
      RingedSpace.Hom.kernelIdealSheaf (zeroSchemeι ℒ s).toShHom :=
  dualIhomUnitHom ℒ ≫
    factorThruImageSubobject (dualSectionHom ℒ s) ≫
      eqToHom
        (congrArg (fun I : X.IdealSubobject ↦ I.toModule)
          (zeroIdealSheaf_toSubobject ℒ s).symm) ≫
      (zeroIdealSheaf ℒ s).toModuleIso.hom

/-- `dualSectionToKernelIdeal` is dual-section factorization followed by the kernel-ideal
comparison. -/
theorem dualSectionToKernelIdeal_def
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) :
    dualSectionToKernelIdeal ℒ s =
      dualIhomUnitHom ℒ ≫
        factorThruImageSubobject (dualSectionHom ℒ s) ≫
          eqToHom
            (congrArg (fun I : X.IdealSubobject ↦ I.toModule)
              (zeroIdealSheaf_toSubobject ℒ s).symm) ≫
          (zeroIdealSheaf ℒ s).toModuleIso.hom := sorry

/-- The canonical surjection from the dual of the pulled-back invertible sheaf onto the
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
    (Scheme.Modules.pullback (zeroSchemeι ℒ s)).map (dualSectionToKernelIdeal ℒ s)

/-- `zeroSchemeIdealSurjection` is the pullback of `dualSectionToKernelIdeal` after the dual
comparison. -/
theorem zeroSchemeIdealSurjection_def
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) :
    zeroSchemeIdealSurjection ℒ s =
      (Scheme.Modules.pullbackDualIso (zeroSchemeι ℒ s) ℒ
          (@Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFreeOfRank
            _ 1 ℒ (Scheme.Modules.isFiniteLocallyFreeOfRankOne_of_invertible ℒ))).inv ≫
        (Scheme.Modules.pullback (zeroSchemeι ℒ s)).map
          (dualSectionToKernelIdeal ℒ s) := sorry

/-- The zero-scheme ideal comparison is an epimorphism. -/
instance zeroSchemeIdealSurjection_epi
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) : Epi (zeroSchemeIdealSurjection ℒ s) := sorry

/-- The zero-scheme immersion of a section of an invertible module is a closed immersion. -/
instance zeroSchemeι_isClosedImmersion
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) : IsClosedImmersion (zeroSchemeι ℒ s) :=
  inferInstanceAs (IsClosedImmersion (zeroIdealSheaf ℒ s).subschemeι)

/-- The canonical rank-one virtual normal bundle of a zero-scheme triple, with module the
pullback of the invertible sheaf. -/
noncomputable def ofZeroScheme
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) :
    VirtualNormalBundle (zeroSchemeι ℒ s) :=
  ofIdealSurjection (zeroSchemeι ℒ s)
    ((Scheme.Modules.pullback (zeroSchemeι ℒ s)).obj ℒ)
    (zeroSchemeIdealSurjection ℒ s)

/-- The module of `ofZeroScheme` is the pullback of the invertible sheaf. -/
theorem ofZeroScheme_module
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) :
    (ofZeroScheme ℒ s).module =
      (Scheme.Modules.pullback (zeroSchemeι ℒ s)).obj ℒ := sorry

/-- The quotient map of `ofZeroScheme` is the zero-scheme ideal surjection followed by the
conormal comparison. -/
theorem ofZeroScheme_map
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) :
    (ofZeroScheme ℒ s).map =
      zeroSchemeIdealSurjection ℒ s ≫
        Conormal.pullbackIdealComparison (zeroSchemeι ℒ s) := sorry

/-- The virtual normal bundle of a zero-scheme triple is finite locally free with an
epimorphic dual-to-conormal map. -/
theorem ofZeroScheme_spec
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) :
    Scheme.Modules.IsFiniteLocallyFree (ofZeroScheme ℒ s).module ∧
      Epi (ofZeroScheme ℒ s).map := sorry

/-- The module of `ofZeroScheme` has rank one. -/
instance ofZeroScheme_module_isFiniteLocallyFreeOfRank
    {X : Scheme.{u}} (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : ℒ.sections) :
    Scheme.Modules.IsFiniteLocallyFreeOfRank 1 (ofZeroScheme ℒ s).module := sorry

end AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
