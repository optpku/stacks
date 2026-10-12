/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

/-!
# Module stalks over an affine base

This file equips the stalk of a scheme module with the scalar action induced by a morphism to an
affine scheme.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R]
variable {X : Scheme.{u}}

/-- The stalk of a scheme module, regarded as a module over an affine base through the composite
`R ⟶ Γ(X, ⊤) ⟶ 𝒪_{X,x}`. -/
noncomputable def stalkMod
    (f : X ⟶ Spec (CommRingCat.of R)) (F : X.Modules) (x : X) : ModuleCat R :=
  @ModuleCat.of R _
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) _
    (@Module.compHom (X.presheaf.stalk x) R
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x) _ _
      (RingedSpace.moduleStalkModule F x) _
      ((X.presheaf.Γgerm x).hom.comp (globalSectionsMap f)))

end AlgebraicGeometry.Scheme.Hom
