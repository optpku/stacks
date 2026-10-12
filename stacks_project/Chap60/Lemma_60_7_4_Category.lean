/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Definition_60_7_2
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

open AlgebraicGeometry CategoryTheory

@[expose] public section

universe u

namespace DividedPowerScheme

/-- The identity morphism of a divided-power scheme. -/
def Hom.id (X : DividedPowerScheme.{u}) : Hom X X where
  base := 𝟙 X.scheme
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- Composition of morphisms of divided-power schemes. -/
def Hom.comp {X Y Z : DividedPowerScheme.{u}}
    (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  ideal_compatible := sorry
  dividedPowers_compatible := sorry

/-- The underlying scheme map of the identity divided-power morphism. -/
lemma Hom.id_base (X : DividedPowerScheme.{u}) :
    (Hom.id X).base = 𝟙 X.scheme := sorry

/-- The underlying scheme map of a composite divided-power morphism. -/
lemma Hom.comp_base {X Y Z : DividedPowerScheme.{u}}
    (f : Hom X Y) (g : Hom Y Z) :
    (Hom.comp f g).base = f.base ≫ g.base := sorry

/-- The canonical category structure on divided-power schemes. -/
instance category : Category DividedPowerScheme where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The morphism induced on the closed subschemes defined by the divided-power ideals. -/
noncomputable def Hom.zeroFiberMap {X Y : DividedPowerScheme.{u}} (f : Hom X Y) :
    X.ideal.subscheme ⟶ Y.ideal.subscheme :=
  Scheme.IdealSheafData.subschemeMap X.ideal Y.ideal f.base
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr f.ideal_compatible)

/-- The zero-fibre morphism commutes with the canonical closed-subscheme immersions. -/
lemma Hom.zeroFiberMap_comm {X Y : DividedPowerScheme.{u}} (f : Hom X Y) :
    f.zeroFiberMap ≫ Y.ideal.subschemeι = X.ideal.subschemeι ≫ f.base := sorry

/-- The zero-fibre map respects composition of divided-power scheme morphisms. -/
lemma Hom.zeroFiberMap_comp {X Y Z : DividedPowerScheme.{u}}
    (f : Hom X Y) (g : Hom Y Z) :
    (Hom.comp f g).zeroFiberMap = f.zeroFiberMap ≫ g.zeroFiberMap := sorry

end DividedPowerScheme
