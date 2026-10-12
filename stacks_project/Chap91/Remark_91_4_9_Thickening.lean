/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Hom

/-!
# Morphisms of first-order thickenings of a fixed ringed space

The canonical under-category morphisms and their contravariant ideal-module maps are
owned by `ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Hom`.
-/

open CategoryTheory
open scoped AlgebraicGeometry

universe u

section

open AlgebraicGeometry.RingedSpace.IsFirstOrderThickening

variable {X X₁ X₂ X₃ : AlgebraicGeometry.RingedSpace.{u}}
variable {i₁ : X ⟶ X₁} {i₂ : X ⟶ X₂} {i₃ : X ⟶ X₃}
variable [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening i₁]
variable [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening i₂]
variable [AlgebraicGeometry.RingedSpace.IsFirstOrderThickening i₃]

#check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom i₁ i₂ : Type u)
#check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.mk :
  (hom : X₁ ⟶ X₂) → i₁ ≫ hom = i₂ → Hom i₁ i₂)
#check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.hom :
  Hom i₁ i₂ → (X₁ ⟶ X₂))
#check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.w :
  ∀ f : Hom i₁ i₂, i₁ ≫ f.hom = i₂)
#check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.id i₁ : Hom i₁ i₁)
#check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.id_hom i₁ :
  (Hom.id i₁).hom = 𝟙 X₁)
#check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.comp :
  Hom i₁ i₂ → Hom i₂ i₃ → Hom i₁ i₃)
#check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.comp_hom :
  ∀ (f : Hom i₁ i₂) (g : Hom i₂ i₃), (f.comp g).hom = f.hom ≫ g.hom)
#check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.idealMap :
  Hom i₁ i₂ →
    (AlgebraicGeometry.RingedSpace.Hom.idealModule i₂ ⟶
      AlgebraicGeometry.RingedSpace.Hom.idealModule i₁))
#check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.idealMap_id i₁ :
  (Hom.id i₁).idealMap = 𝟙 (AlgebraicGeometry.RingedSpace.Hom.idealModule i₁))
#check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.Hom.idealMap_comp :
  ∀ (f : Hom i₁ i₂) (g : Hom i₂ i₃),
    (f.comp g).idealMap = g.idealMap ≫ f.idealMap)

end
