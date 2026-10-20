/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Integral.Complement
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafPullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianSupport
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A sheaf of sets restricts to the terminal sheaf on the complement of an integral image. -/
def restrictsToTerminalOnImageComplement [IsIntegralHom f]
    (F : Sheaf Y.smallEtaleTopology (Type u)) : Prop :=
  Nonempty
    (((Scheme.smallEtalePullback (integralImageComplement f).ι).sheafPullback
        (Type u) Y.smallEtaleTopology
        (integralImageComplement f).toScheme.smallEtaleTopology).obj F ≅
      ⊤_ (Sheaf (integralImageComplement f).toScheme.smallEtaleTopology (Type u)))

/-- Restriction to the integral image complement is isomorphic to the terminal sheaf
if and only if the restricted sheaf is terminal. -/
theorem restrictsToTerminalOnImageComplement_iff [IsIntegralHom f]
    (F : Sheaf Y.smallEtaleTopology (Type u)) :
    restrictsToTerminalOnImageComplement f F ↔
      Nonempty (IsTerminal
        (((Scheme.smallEtalePullback (integralImageComplement f).ι).sheafPullback
          (Type u) Y.smallEtaleTopology
          (integralImageComplement f).toScheme.smallEtaleTopology).obj F)) := sorry

variable [IsIntegralHom f] [UniversallyInjective f]

/-- Small-étale direct image of sets along an integral universally injective morphism is full. -/
@[instance]
theorem smallEtalePushforward_integralUnivInj_type_full :
    (Scheme.smallEtaleDirectImage.{u,u} f).Full := sorry

/-- Small-étale direct image of sets along an integral universally injective morphism
is faithful. -/
@[instance]
theorem smallEtalePushforward_integralUnivInj_type_faithful :
    (Scheme.smallEtaleDirectImage.{u,u} f).Faithful := sorry

/-- A sheaf of sets lies in the essential image of direct image along an integral
universally injective morphism exactly when its restriction off the image is terminal. -/
theorem mem_essImage_smallEtalePushforward_type_iff
    (F : Sheaf Y.smallEtaleTopology (Type u)) :
    (Scheme.smallEtaleDirectImage.{u,u} f).essImage F ↔
      restrictsToTerminalOnImageComplement f F := sorry

/-- The inverse-image/direct-image counit for sets is invertible along an integral
universally injective morphism of schemes. -/
@[instance]
theorem isIso_counit_smallEtalePushforward_integralUnivInj_type :
    IsIso ((Scheme.smallEtalePullback f).sheafAdjunctionContinuous
      (Type u) Y.smallEtaleTopology X.smallEtaleTopology).counit := sorry

/-- Small-étale direct image of abelian sheaves along an integral universally injective
morphism is full. -/
@[instance]
theorem smallEtalePushforward_integralUnivInj_ab_full :
    (smallEtalePushforwardAb f).Full := sorry

/-- Small-étale direct image of abelian sheaves along an integral universally injective
morphism is faithful. -/
@[instance]
theorem smallEtalePushforward_integralUnivInj_ab_faithful :
    (smallEtalePushforwardAb f).Faithful := sorry

/-- An abelian sheaf lies in the essential image of direct image along an integral
universally injective morphism exactly when its support is contained in the image. -/
theorem mem_essImage_smallEtalePushforward_ab_iff
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (smallEtalePushforwardAb f).essImage F ↔
      abelianSheafSupport F ⊆ Set.range f.base := sorry

/-- The inverse-image/direct-image counit for abelian sheaves is invertible along an integral
universally injective morphism of schemes. -/
@[instance]
theorem isIso_counit_smallEtalePushforward_integralUnivInj_ab :
    IsIso ((Scheme.smallEtalePullback f).sheafAdjunctionContinuous
      AddCommGrpCat.{u} Y.smallEtaleTopology X.smallEtaleTopology).counit := sorry

end AlgebraicGeometry.Scheme.Etale
