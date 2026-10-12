/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Stalks of restricted module sheaves

This file records the canonical additive map on stalks induced by a morphism between module
sheaves restricted to an open subscheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A morphism between restrictions of two module sheaves to an open neighborhood induces an
additive homomorphism between their stalks at the ambient point. -/
noncomputable def stalkAddHomOfRestrictHom
    {X : Scheme.{u}} {G F : X.Modules} (x : X)
    (U : X.Opens) (hxU : x ∈ U)
    (φ : (restrictFunctor U.ι).obj G ⟶ (restrictFunctor U.ι).obj F) :
    (toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).obj G ⟶
      (toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).obj F :=
  let xU : (U : Scheme) := ⟨x, hxU⟩
  (restrictStalkNatIso U.ι xU).inv.app G ≫
    (toPresheaf (U : Scheme) ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} xU).map φ ≫
    (restrictStalkNatIso U.ι xU).hom.app F

end AlgebraicGeometry.Scheme.Modules
