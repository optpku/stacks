/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Construction
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Construction
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

/-!
# Fibre-product comparison after a map of algebraic stacks

Morphisms `f : X ⟶ Z`, `g : Y ⟶ Z`, and `h : Z ⟶ T` induce
`X ×_Z Y ⟶ X ×_T Y` as the `TwoFibreProduct.map` of the identity-on-sources
cospan transformation with base `h`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The identity-on-sources cospan transformation with base `h`, sending the
cospan `f, g` to `f ≫ h, g ≫ h`. -/
def mapDescCospan {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    CospanTransform f g (f ≫ h) (g ≫ h) :=
  CospanTransform.mk (𝟙 X) (𝟙 Y) h (λ_ (f ≫ h)) (λ_ (g ≫ h))

/-- The left vertex of `mapDescCospan f g h` is the identity of `X`. -/
theorem mapDescCospan_left {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (mapDescCospan f g h).left = 𝟙 X :=
  sorry

/-- The right vertex of `mapDescCospan f g h` is the identity of `Y`. -/
theorem mapDescCospan_right {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (mapDescCospan f g h).right = 𝟙 Y :=
  sorry

/-- The base vertex of `mapDescCospan f g h` is `h`. -/
theorem mapDescCospan_base {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (mapDescCospan f g h).base = h :=
  sorry

/-- The left generating comparison of `mapDescCospan f g h` is the left unitor
of `f ≫ h`. -/
theorem mapDescCospan_leftIso {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (mapDescCospan f g h).leftIso = λ_ (f ≫ h) :=
  sorry

/-- The right generating comparison of `mapDescCospan f g h` is the left unitor
of `g ≫ h`. -/
theorem mapDescCospan_rightIso {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    (mapDescCospan f g h).rightIso = λ_ (g ≫ h) :=
  sorry

/-- The comparison 1-morphism `X ×_Z Y ⟶ X ×_T Y` induced by `h`. -/
def mapDesc {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u} (f ≫ h) (g ≫ h) :=
  TwoFibreProduct.map (mapDescCospan f g h)

/-- `mapDesc f g h` is the two-fibre-product map of `mapDescCospan f g h`. -/
theorem mapDesc_eq {S : Scheme.{u}} {X Y Z T : GroupoidsOver S}
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ T) :
    mapDesc f g h = TwoFibreProduct.map (mapDescCospan f g h) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
