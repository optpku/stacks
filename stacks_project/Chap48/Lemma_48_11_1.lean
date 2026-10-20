/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coextension
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry
namespace Scheme

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f]
variable (ℱ : X.Modules) (U : X.Opens) (hU : IsAffineOpen U)

/- Lemma 48.11.1 (1): for an affine morphism `f : Y ⟶ X`, coextension along
`𝒪_X ⟶ f_*𝒪_Y` is right adjoint to restriction of scalars. -/
@[stacks 0BUZ] #check
  (SheafOfModules.RingedSite.restrictionCoextendAdj
      (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom) :
    SheafOfModules.RingedSite.restrictionAlong.{u, u, u, u}
        (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom) ⊣
      SheafOfModules.RingedSite.coextendAlong.{u, u, u}
        (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom))

/- Lemma 48.11.1 (2): if `f : Y ⟶ X` is affine and `U ⊆ X` is affine, then the
sections on `U` of the coextension of `ℱ` along `𝒪_X ⟶ f_*𝒪_Y` are isomorphic to
`Hom_{Γ(X, U)}(Γ(Y, f⁻¹(U)), Γ(U, ℱ))`, bundled as a module over
`Γ(Y, f⁻¹(U))`. -/
@[stacks 0BUZ] #check
  (AlgebraicGeometry.Scheme.coextendStructureSheaf_sections_isomorphic
      f ℱ U hU :
    IsIsomorphic
      (((SheafOfModules.RingedSite.coextendAlong
        (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)).obj ℱ).val.obj
          (Opposite.op U))
      ((ModuleCat.coextendScalars
        (Scheme.Hom.sectionsMapAlong f U (f ⁻¹ᵁ U) le_rfl)).obj
          (ℱ.val.obj (Opposite.op U))))

end Scheme
end AlgebraicGeometry
