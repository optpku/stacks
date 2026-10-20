/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower.Multiplication
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Rees
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Blowup

variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- The degree-`i` tensor-power twist of the exceptional divisor on a blowup. -/
noncomputable abbrev exceptionalTwist (π : Blowup X I) (i : ℕ) : π.scheme.Modules :=
  RingedSpace.TensorPower.sheaf
    (@Scheme.IdealSheafData.associatedSheaf π.scheme π.exceptionalDivisor
      π.isBlowup.toIsEffectiveCartierDivisor) i

/-- The canonical section of the exceptional divisor, raised to the `i`th tensor power. -/
noncomputable def exceptionalTwistSectionHom (π : Blowup X I) :
    (i : ℕ) → SheafOfModules.unit π.scheme.ringCatSheaf ⟶ π.exceptionalTwist i
  | 0 => RingedSpace.TensorPower.one _
  | i + 1 =>
      (RingedSpace.unitIsoTensorUnit π.scheme.toRingedSpace).hom ≫
        (λ_ (𝟙_ π.scheme.Modules)).inv ≫
        @tensorHom π.scheme.Modules _
          (RingedSpace.modulesMonoidalCategory
            π.scheme.toRingedSpace).toMonoidalCategoryStruct _ _ _ _
          (((RingedSpace.unitIsoTensorUnit π.scheme.toRingedSpace).inv ≫
            ((@Scheme.IdealSheafData.associatedSheaf π.scheme π.exceptionalDivisor
                π.isBlowup.toIsEffectiveCartierDivisor).unitHomEquiv.symm
              (@Scheme.IdealSheafData.canonicalSection π.scheme π.exceptionalDivisor
                π.isBlowup.toIsEffectiveCartierDivisor))) :
            (𝟙_ π.scheme.Modules) ⟶
              @Scheme.IdealSheafData.associatedSheaf π.scheme π.exceptionalDivisor
                π.isBlowup.toIsEffectiveCartierDivisor)
          (((RingedSpace.unitIsoTensorUnit π.scheme.toRingedSpace).inv ≫
            exceptionalTwistSectionHom π i) :
              (𝟙_ π.scheme.Modules) ⟶ π.exceptionalTwist i)

/-- The zeroth exceptional-divisor section power is the tensor-power unit. -/
theorem exceptionalTwistSectionHom_zero (π : Blowup X I) :
    π.exceptionalTwistSectionHom 0 =
      RingedSpace.TensorPower.one
        (@Scheme.IdealSheafData.associatedSheaf π.scheme π.exceptionalDivisor
          π.isBlowup.toIsEffectiveCartierDivisor) := sorry

/-- Exceptional-divisor section powers are obtained by tensoring once more with the canonical
section. -/
theorem exceptionalTwistSectionHom_succ (π : Blowup X I) (i : ℕ) :
    π.exceptionalTwistSectionHom (i + 1) =
      (RingedSpace.unitIsoTensorUnit π.scheme.toRingedSpace).hom ≫
        (λ_ (𝟙_ π.scheme.Modules)).inv ≫
        @tensorHom π.scheme.Modules _
          (RingedSpace.modulesMonoidalCategory
            π.scheme.toRingedSpace).toMonoidalCategoryStruct _ _ _ _
          (((RingedSpace.unitIsoTensorUnit π.scheme.toRingedSpace).inv ≫
            ((@Scheme.IdealSheafData.associatedSheaf π.scheme π.exceptionalDivisor
                π.isBlowup.toIsEffectiveCartierDivisor).unitHomEquiv.symm
              (@Scheme.IdealSheafData.canonicalSection π.scheme π.exceptionalDivisor
                π.isBlowup.toIsEffectiveCartierDivisor))) :
            (𝟙_ π.scheme.Modules) ⟶
              @Scheme.IdealSheafData.associatedSheaf π.scheme π.exceptionalDivisor
                π.isBlowup.toIsEffectiveCartierDivisor)
          (((RingedSpace.unitIsoTensorUnit π.scheme.toRingedSpace).inv ≫
            π.exceptionalTwistSectionHom i) :
              (𝟙_ π.scheme.Modules) ⟶ π.exceptionalTwist i) := sorry

/-- The underived adjoint of the canonical map to a pushed-forward twisted pullback. -/
noncomputable def exceptionalTwistAdjoint (π : Blowup X I) (𝓔 : X.Modules) (i : ℕ) :
    𝓔 ⟶ (Scheme.Modules.pushforward π.hom).obj
      ((Scheme.Modules.pullback π.hom).obj 𝓔 ⊗ π.exceptionalTwist i) :=
  (Scheme.Modules.pullbackPushforwardAdjunction π.hom).homEquiv _ _
    ((ρ_ ((Scheme.Modules.pullback π.hom).obj 𝓔)).inv ≫
      tensorHom (𝟙 _)
        ((RingedSpace.unitIsoTensorUnit π.scheme.toRingedSpace).inv ≫
          π.exceptionalTwistSectionHom i))

/-- Transposing the exceptional-twist adjoint back recovers the section-power tensor map. -/
theorem exceptionalTwistAdjoint_adj (π : Blowup X I) (𝓔 : X.Modules) (i : ℕ) :
    ((Scheme.Modules.pullbackPushforwardAdjunction π.hom).homEquiv _ _).symm
      (π.exceptionalTwistAdjoint 𝓔 i) =
      (ρ_ ((Scheme.Modules.pullback π.hom).obj 𝓔)).inv ≫
        tensorHom (𝟙 _)
          ((RingedSpace.unitIsoTensorUnit π.scheme.toRingedSpace).inv ≫
            π.exceptionalTwistSectionHom i) := sorry

/-- The derived comparison from a module in degree zero to the pushforward of its twisted
pullback in degree zero. -/
noncomputable def exceptionalTwistComparison (π : Blowup X I) (𝓔 : X.Modules) (i : ℕ) :
    (DerivedCategory.singleFunctor X.Modules 0).obj 𝓔 ⟶
      (RingedSpace.moduleDerivedPushforward π.hom.toShHom).obj
        ((DerivedCategory.singleFunctor π.scheme.Modules 0).obj
          ((Scheme.Modules.pullback π.hom).obj 𝓔 ⊗ π.exceptionalTwist i)) :=
  RingedSpace.moduleDerivedPushforward.comparison π.hom.toShHom 𝓔
    ((Scheme.Modules.pullback π.hom).obj 𝓔 ⊗ π.exceptionalTwist i)
    (π.exceptionalTwistAdjoint 𝓔 i)

/-- The exceptional-twist comparison is the standard derived-pushforward comparison for its
underived adjoint. -/
theorem exceptionalTwistComparison_def (π : Blowup X I) (𝓔 : X.Modules) (i : ℕ) :
    π.exceptionalTwistComparison 𝓔 i =
      RingedSpace.moduleDerivedPushforward.comparison π.hom.toShHom 𝓔
        ((Scheme.Modules.pullback π.hom).obj 𝓔 ⊗ π.exceptionalTwist i)
        (π.exceptionalTwistAdjoint 𝓔 i) := sorry

end AlgebraicGeometry.Blowup
