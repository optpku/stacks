/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

/-!
# Coextension of sheaves of modules on schemes

This module contains the affine-open section computation for coextension along
the structure-sheaf map associated to an affine morphism of schemes.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- If `f : Y ⟶ X` is affine and `U ⊆ X` is affine, then the sections on `U` of
the coextension of `ℱ` along `𝒪_X ⟶ f_*𝒪_Y` are isomorphic to
`Hom_{Γ(X, U)}(Γ(Y, f⁻¹(U)), Γ(U, ℱ))`, bundled as a module over
`Γ(Y, f⁻¹(U))`. -/
@[stacks 0BUZ]
theorem coextendStructureSheaf_sections_isomorphic
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsAffineHom f] (ℱ : X.Modules)
    (U : X.Opens) (hU : IsAffineOpen U) :
    IsIsomorphic
      (((SheafOfModules.RingedSite.coextendAlong
        (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)).obj ℱ).val.obj
          (Opposite.op U))
      ((ModuleCat.coextendScalars
        (Scheme.Hom.sectionsMapAlong f U (f ⁻¹ᵁ U) le_rfl)).obj
          (ℱ.val.obj (Opposite.op U))) := sorry

end AlgebraicGeometry.Scheme
