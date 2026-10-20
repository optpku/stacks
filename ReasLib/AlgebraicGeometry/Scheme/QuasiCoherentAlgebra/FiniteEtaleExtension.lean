/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Definition
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Depth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The raw `𝒪_X`-algebra object given by the pushforward of `𝒪_V` along `π ≫ j`. -/
def finiteEtaleExtensionAlgebra_obj {U X V : Scheme.{u}} (j : U ⟶ X) (π : V ⟶ U) :
    Under (schemeCommRingSheaf X) :=
  Under.mk (RingedSpace.Hom.commRingSheafPushforwardMap (π ≫ j).toShHom)

/-- The pushforward of the structure sheaf of a finite étale cover along an open immersion
with complement of depth at least two, regarded as a quasi-coherent algebra. -/
def finiteEtaleExtensionAlgebra {U X V : Scheme.{u}} (j : U ⟶ X) (π : V ⟶ U)
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsOpenImmersion j]
    [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ Set.range j.base →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    X.QcAlgebraUnder :=
  ⟨finiteEtaleExtensionAlgebra_obj j π, sorry⟩

/-- The underlying algebra of the finite étale extension is the raw pushforward algebra. -/
theorem finiteEtaleExtensionAlgebra_obj_eq {U X V : Scheme.{u}} (j : U ⟶ X) (π : V ⟶ U)
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsOpenImmersion j]
    [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ Set.range j.base →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    (finiteEtaleExtensionAlgebra j π hdepth).obj = finiteEtaleExtensionAlgebra_obj j π := sorry

end AlgebraicGeometry.Scheme
