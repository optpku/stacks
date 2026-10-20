/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Map
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.Derived.Coefficients
public import ReasLib.AlgebraicGeometry.Scheme.Module.DifferentialOperator.Derived.RelativeCupProduct
public import ReasLib.CategoryTheory.Filtration.Complex.Convergence
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape
open DerivedCategory.DerivedTensor
open DerivedCategory.DerivedTensor.Bifunctor
open FilteredComplex.Cohomology.Convergence
open SheafOfModules.RingedSite RingedSite.Hom
open AlgebraicGeometry.Scheme.Modules.Kunneth
open AlgebraicGeometry.Scheme.RelativeCupProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/-- The coefficient-site morphism implementing restriction of scalars from `𝒪_Y` to
`b⁻¹𝒪_S`. -/
noncomputable abbrev scalarRestrictionHom {Y S : Scheme.{u}} (b : Y ⟶ S) :=
  RingedSpace.DeRham.baseChangeHom
    (((CommSq.mk rfl : CommSq (𝟙 Y) (𝟙 Y) b b)).map
      (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace))

/-- The coefficient-site direct-image morphism associated to a morphism of schemes over `S`. -/
noncomputable abbrev relativePushforwardHom {X Y S : Scheme.{u}}
    {f : X ⟶ Y} {a : X ⟶ S} {b : Y ⟶ S}
    (sq : CommSq f a b (𝟙 S)) :=
  RingedSpace.DeRham.baseChangeHom
    (sq.map
      (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace))

/-- The sheaf `Ω^p_{Y/S}`, concentrated in degree zero and regarded as a derived
`𝒪_Y`-module through the identity coefficient site. -/
noncomputable abbrev formDerived {Y S : Scheme.{u}} (b : Y ⟶ S) (p : ℕ) :
    CoefficientDerived (𝟙 Y) :=
  (@DerivedCategory.singleFunctor
    (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
      (coefficientSite (𝟙 Y))) 0).obj
      ((restrictionAlong
        (Hom.FiniteOrderDifferentialOperatorCat.coefficientMap (𝟙 Y))).obj
          (RingedSpace.DeRham.form b.toLRSHom.toShHom p))

/-- The `E₁`-page term
`H^q(Ω^p_{Y/S} ⊗ᴸ_{𝒪_Y} Rf_* Ω^•_{X/Y})`, restricted to `b⁻¹𝒪_S`. -/
noncomputable abbrev relativePageOneTerm {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (b : Y ⟶ S) (p : ℕ) (q : ℤ)
    [hPush : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u}
        (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u, u, u, u} (coefficientSite f))]
    [hRestr : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (scalarRestrictionHom b))
      (ModuleQis.{u, u, u, u} (coefficientSite (𝟙 Y)))]
    [hTensor : @Has
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (coefficientSite (𝟙 Y)))
      _ _ _ _ _ _ _] :
    RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b) :=
  (@DerivedCategory.homologyFunctor
    (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b)) _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
      (coefficientSite b)) q).obj
      ((@modulePushforwardDerived.{u, u, u, u, u, u}
          _ _ (scalarRestrictionHom b) inferInstance inferInstance hRestr).obj
        (((@coefficientDerivedTensor _ _ (𝟙 Y) hTensor).obj (formDerived b p)).obj
          ((@modulePushforwardDerived.{u, u, u, u, u, u}
              _ _ (DerivedPushforward.pushforwardHom f) inferInstance inferInstance hPush).obj
            (DerivedPushforward.derivedComplex f))))

/-- The degree-`n` derived direct image `R^n f_* Ω^•_{X/S}`, viewed as a
`b⁻¹𝒪_S`-module on `Y`. -/
noncomputable abbrev relativeAbutment {X Y S : Scheme.{u}}
    {f : X ⟶ Y} {a : X ⟶ S} {b : Y ⟶ S}
    (sq : CommSq f a b (𝟙 S)) (n : ℤ)
    [hRelative : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (relativePushforwardHom sq))
      (ModuleQis.{u, u, u, u} (coefficientSite a))] :
    RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b) :=
  (@DerivedCategory.homologyFunctor
    (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b)) _ _
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
      (coefficientSite b)) n).obj
      ((@modulePushforwardDerived.{u, u, u, u, u, u}
          _ _ (relativePushforwardHom sq) inferInstance inferInstance hRelative).obj
        (DerivedPushforward.derivedComplex a))

/-- For a smooth morphism of schemes over a base, the filtered relative de Rham complex
produces a bounded cohomological spectral sequence with the displayed derived page and
abutment identifications, converging to the filtered-complex homology. -/
theorem existsRelativeSpectralSequence {X Y S : Scheme.{u}}
    (f : X ⟶ Y) (a : X ⟶ S) (b : Y ⟶ S)
    (sq : CommSq f a b (𝟙 S)) [QuasiCompact f] [QuasiSeparated f] [Smooth f]
    [hPush : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u}
        (DerivedPushforward.pushforwardHom f))
      (ModuleQis.{u, u, u, u} (coefficientSite f))]
    [hRestr : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (scalarRestrictionHom b))
      (ModuleQis.{u, u, u, u} (coefficientSite (𝟙 Y)))]
    [hRelative : Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{u, u, u, u, u, u} (relativePushforwardHom sq))
      (ModuleQis.{u, u, u, u} (coefficientSite a))]
    [hTensor : @Has
      (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite (𝟙 Y))) _ _
      (RingedSite.Hom.moduleCat_hasDerivedCategory.{u, u, u, u}
        (coefficientSite (𝟙 Y)))
      _ _ _ _ _ _ _] :
    ∃ (K : FilteredComplex (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b)))
      (E : CohomologicalSpectralSequence
        (RingedSite.ModuleCat.{u, u, u, u} (coefficientSite b)) 0)
      (associated : K.IsAssociated E)
      (pageOneIso : ∀ (p : ℕ) (q : ℤ),
        (E.page 1 zero_le_one).X ((p : ℤ), q) ≅
          @relativePageOneTerm X Y S f b p q hPush hRestr hTensor)
      (abutmentIso : ∀ n : ℤ,
        K.underlying.homology n ≅ @relativeAbutment X Y S f a b sq n hRelative),
      E.IsBounded ∧ Converges K E := sorry

end AlgebraicGeometry.Scheme.DeRham
