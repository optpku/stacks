/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.ExceptionalTwist

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Blowup

variable {X : Scheme.{u}} {I : X.IdealSheafData}
variable (π : Blowup X I) (𝓔 : X.Modules) (i : ℕ)

#check (π.exceptionalTwist i : π.scheme.Modules)

#check (π.exceptionalTwistSectionHom :
  (j : ℕ) → SheafOfModules.unit π.scheme.ringCatSheaf ⟶ π.exceptionalTwist j)

#check (π.exceptionalTwistSectionHom_zero :
  π.exceptionalTwistSectionHom 0 =
    RingedSpace.TensorPower.one
      (@Scheme.IdealSheafData.associatedSheaf π.scheme π.exceptionalDivisor
        π.isBlowup.toIsEffectiveCartierDivisor))

#check (π.exceptionalTwistSectionHom_succ i :
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
            (𝟙_ π.scheme.Modules) ⟶ π.exceptionalTwist i))

#check (π.exceptionalTwistAdjoint 𝓔 i :
  𝓔 ⟶ (Scheme.Modules.pushforward π.hom).obj
    ((Scheme.Modules.pullback π.hom).obj 𝓔 ⊗ π.exceptionalTwist i))

#check (π.exceptionalTwistAdjoint_adj 𝓔 i :
  ((Scheme.Modules.pullbackPushforwardAdjunction π.hom).homEquiv _ _).symm
    (π.exceptionalTwistAdjoint 𝓔 i) =
    (ρ_ ((Scheme.Modules.pullback π.hom).obj 𝓔)).inv ≫
      tensorHom (𝟙 _)
        ((RingedSpace.unitIsoTensorUnit π.scheme.toRingedSpace).inv ≫
          π.exceptionalTwistSectionHom i))

#check (π.exceptionalTwistComparison 𝓔 i :
  (DerivedCategory.singleFunctor X.Modules 0).obj 𝓔 ⟶
    (RingedSpace.moduleDerivedPushforward π.hom.toShHom).obj
      ((DerivedCategory.singleFunctor π.scheme.Modules 0).obj
        ((Scheme.Modules.pullback π.hom).obj 𝓔 ⊗ π.exceptionalTwist i)))

#check (π.exceptionalTwistComparison_def 𝓔 i :
  π.exceptionalTwistComparison 𝓔 i =
    RingedSpace.moduleDerivedPushforward.comparison π.hom.toShHom 𝓔
      ((Scheme.Modules.pullback π.hom).obj 𝓔 ⊗ π.exceptionalTwist i)
      (π.exceptionalTwistAdjoint 𝓔 i))

end AlgebraicGeometry.Blowup
