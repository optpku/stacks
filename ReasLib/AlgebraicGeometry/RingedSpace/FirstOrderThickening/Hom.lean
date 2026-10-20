module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Morphisms of first-order thickenings

Morphisms of first-order thickenings of a fixed ringed space are morphisms in its
under category. They induce contravariant maps of ideal modules.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IsFirstOrderThickening

/-- A morphism of first-order thickenings of `X` is a commuting triangle under `X`. -/
abbrev Hom {X X₁ X₂ : RingedSpace.{u}} (i₁ : X ⟶ X₁) (i₂ : X ⟶ X₂)
    [IsFirstOrderThickening i₁] [IsFirstOrderThickening i₂] :=
  Under.mk i₁ ⟶ Under.mk i₂

/-- A commuting triangle gives a morphism of first-order thickenings. -/
def Hom.mk {X X₁ X₂ : RingedSpace.{u}} {i₁ : X ⟶ X₁} {i₂ : X ⟶ X₂}
    [IsFirstOrderThickening i₁] [IsFirstOrderThickening i₂]
    (hom : X₁ ⟶ X₂) (w : i₁ ≫ hom = i₂) : Hom i₁ i₂ :=
  Under.homMk hom w

/-- The underlying ringed-space morphism of a morphism of first-order thickenings. -/
abbrev Hom.hom {X X₁ X₂ : RingedSpace.{u}} {i₁ : X ⟶ X₁} {i₂ : X ⟶ X₂}
    [IsFirstOrderThickening i₁] [IsFirstOrderThickening i₂] (f : Hom i₁ i₂) :
    X₁ ⟶ X₂ :=
  Under.Hom.right f

/-- A morphism of first-order thickenings commutes with the inclusions of the base. -/
theorem Hom.w {X X₁ X₂ : RingedSpace.{u}} {i₁ : X ⟶ X₁} {i₂ : X ⟶ X₂}
    [IsFirstOrderThickening i₁] [IsFirstOrderThickening i₂] (f : Hom i₁ i₂) :
    i₁ ≫ f.hom = i₂ := sorry

/-- The identity morphism of a first-order thickening. -/
def Hom.id {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i] :
    Hom i i :=
  𝟙 (Under.mk i)

/-- The underlying morphism of the identity is the identity on the ambient thickening. -/
theorem Hom.id_hom {X X' : RingedSpace.{u}} (i : X ⟶ X')
    [IsFirstOrderThickening i] :
    (Hom.id i).hom = 𝟙 X' := sorry

/-- Composition of morphisms of first-order thickenings of a fixed ringed space. -/
def Hom.comp {X X₁ X₂ X₃ : RingedSpace.{u}}
    {i₁ : X ⟶ X₁} {i₂ : X ⟶ X₂} {i₃ : X ⟶ X₃}
    [IsFirstOrderThickening i₁] [IsFirstOrderThickening i₂]
    [IsFirstOrderThickening i₃] (f : Hom i₁ i₂) (g : Hom i₂ i₃) :
    Hom i₁ i₃ :=
  f ≫ g

/-- The underlying morphism of a composite is the composite of the underlying morphisms. -/
theorem Hom.comp_hom {X X₁ X₂ X₃ : RingedSpace.{u}}
    {i₁ : X ⟶ X₁} {i₂ : X ⟶ X₂} {i₃ : X ⟶ X₃}
    [IsFirstOrderThickening i₁] [IsFirstOrderThickening i₂]
    [IsFirstOrderThickening i₃] (f : Hom i₁ i₂) (g : Hom i₂ i₃) :
    (f.comp g).hom = f.hom ≫ g.hom := sorry

/-- The contravariant map `ℐ₂ ⟶ ℐ₁` of ideal modules induced by a thickening morphism. -/
noncomputable def Hom.idealMap {X X₁ X₂ : RingedSpace.{u}}
    {i₁ : X ⟶ X₁} {i₂ : X ⟶ X₂}
    [IsFirstOrderThickening i₁] [IsFirstOrderThickening i₂] (f : Hom i₁ i₂) :
    RingedSpace.Hom.idealModule i₂ ⟶ RingedSpace.Hom.idealModule i₁ :=
  RingedSpace.Hom.idealMap f.hom f.w

/-- The identity morphism of a first-order thickening induces the identity on its ideal module. -/
theorem Hom.idealMap_id {X X' : RingedSpace.{u}} (i : X ⟶ X')
    [IsFirstOrderThickening i] :
    (Hom.id i).idealMap = 𝟙 (RingedSpace.Hom.idealModule i) := sorry

/-- Ideal-module maps compose contravariantly under composition of thickening morphisms. -/
theorem Hom.idealMap_comp {X X₁ X₂ X₃ : RingedSpace.{u}}
    {i₁ : X ⟶ X₁} {i₂ : X ⟶ X₂} {i₃ : X ⟶ X₃}
    [IsFirstOrderThickening i₁] [IsFirstOrderThickening i₂]
    [IsFirstOrderThickening i₃] (f : Hom i₁ i₂) (g : Hom i₂ i₃) :
    (f.comp g).idealMap = g.idealMap ≫ f.idealMap := sorry

/-- The structure-sheaf map of a first-order thickening is locally surjective. -/
instance commRingSheafPushforwardMap_isLocallySurjective
    {Y Y' : RingedSpace.{u}} (i : Y ⟶ Y') [IsFirstOrderThickening i] :
    Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i) :=
  IsThickening.c_locallySurjective

end AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
