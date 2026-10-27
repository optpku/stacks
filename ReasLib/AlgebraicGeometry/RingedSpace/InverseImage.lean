/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-! # Inverse-image ringed spaces and restriction of scalars -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.RingedSpace AlgebraicGeometry.RingedSpace.Hom
open TopologicalSpace Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/-- The ringed space (Y, g⁻¹ 𝒪_X) obtained by pulling back the structure sheaf of
X along the underlying map of g. -/
def inverseImageSpace (g : Y ⟶ X) : RingedSpace.{u} :=
  ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf).toRingedSpace

/-- The structure sheaf of `inverseImageSpace g` is g⁻¹ 𝒪_X. -/
theorem inverseImageSpace_sheaf (g : Y ⟶ X) :
    (inverseImageSpace g).sheaf =
      (TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj X.sheaf := rfl

/-- The canonical morphism (Y, g⁻¹ 𝒪_X) ⟶ X with underlying map g and unit
structure map 𝒪_X ⟶ g_* g⁻¹ 𝒪_X. -/
def inverseImageTo (g : Y ⟶ X) : inverseImageSpace g ⟶ X :=
  InducedCategory.homMk
    { base := g.hom.base
      c :=
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
            g.hom.base).unit.app X.sheaf).hom }

/-- The underlying continuous map of `inverseImageTo g` is the underlying map of g. -/
theorem inverseImageTo_base (g : Y ⟶ X) :
    (inverseImageTo g).hom.base = g.hom.base := rfl

/-- The morphism Y ⟶ (Y, g⁻¹ 𝒪_X) with identity underlying map and structure map
g^♯ : g⁻¹ 𝒪_X ⟶ 𝒪_Y. -/
def fromInverseImage (g : Y ⟶ X) : Y ⟶ inverseImageSpace g :=
  InducedCategory.homMk
    { base := 𝟙 Y.carrier
      c := (inverseImageStructureSheafHomComm g).hom }

/-- The underlying continuous map of `fromInverseImage g` is the identity on Y. -/
theorem fromInverseImage_base (g : Y ⟶ X) :
    (fromInverseImage g).hom.base = 𝟙 Y.carrier := rfl

/-- The two canonical morphisms recover g. -/
theorem fromInverseImage_comp (g : Y ⟶ X) :
    fromInverseImage g ≫ inverseImageTo g = g := sorry

/-- Restriction of scalars of an 𝒪_Y-module along g^♯, as a module on
(Y, g⁻¹ 𝒪_X). -/
def restrictToInverseImage (g : Y ⟶ X) (G : Y.Modules) :
    (inverseImageSpace g).Modules :=
  ((fromInverseImage g) _*).obj G

/-- `restrictToInverseImage` is pushforward of modules along `fromInverseImage`. -/
theorem restrictToInverseImage_spec (g : Y ⟶ X) (G : Y.Modules) :
    restrictToInverseImage g G = ((fromInverseImage g) _*).obj G := rfl

/-- Restriction of scalars along `fromInverseImage` preserves finite limits. -/
instance instPreservesFiniteLimits_fromInverseImage_pushforward (g : Y ⟶ X) :
    PreservesFiniteLimits ((fromInverseImage g)_*) := sorry

/-- Restriction of scalars along `fromInverseImage` preserves finite colimits. -/
instance instPreservesFiniteColimits_fromInverseImage_pushforward (g : Y ⟶ X) :
    PreservesFiniteColimits ((fromInverseImage g)_*) := sorry

end AlgebraicGeometry.RingedSpace
