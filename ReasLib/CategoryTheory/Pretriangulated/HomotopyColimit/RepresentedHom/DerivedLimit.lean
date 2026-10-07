module

public import ReasLib.CategoryTheory.InverseSystem.Milnor.Derived
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.RepresentedHom.Cone
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Equiv
import Mathlib.Tactic.CrossRefAttribute

/-!
# The first-derived-limit map for represented Hom

@stack 0CQX

This leaf constructs the map from the product of the shifted represented Hom tower to
`Hom_D(X, L)` and descends it through the canonical Milnor quotient.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit.RepresentedHom

open SequentialInverseSystem.Milnor.ProductCone

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The selected product of the shifted represented Hom tower. -/
@[stacks 0CQX]
abbrev shiftedProduct (K : ℕ ⥤ D) (L : D) : AddCommGrpCat :=
  ∏ᶜ (shiftedTower K L).family

/-- An element of the product of shifted represented Hom groups determines a cocone from the
discrete family of the `K_n` to `L[-1]`. -/
@[stacks 0CQX]
def shiftedProductCocone (K : ℕ ⥤ D) (L : D)
    (x : shiftedProduct K L) : Cocone (Discrete.functor K.obj) :=
  Cocone.mk (L⟦(-1 : ℤ)⟧) <| Discrete.natTrans fun n ↦
    (Pi.π (shiftedTower K L).family n.as) x

/-- The `n`th leg of `shiftedProductCocone` is the `n`th coordinate of the supplied product
element. -/
@[simp]
theorem shiftedProductCocone_ι_app (K : ℕ ⥤ D) (L : D)
    (x : shiftedProduct K L) (n : ℕ) :
    (shiftedProductCocone K L x).ι.app ⟨n⟩ =
      (Pi.π (shiftedTower K L).family n) x := sorry

/-- The morphism from the stored coproduct to `L[-1]` classified by an element of the shifted
Hom product. -/
@[stacks 0CQX]
def shiftedProductDesc {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D)
    (x : shiftedProduct K L) : P.coproduct.cocone.pt ⟶ L⟦(-1 : ℤ)⟧ :=
  P.coproduct.isColimit.desc (shiftedProductCocone K L x)

/-- Restricting `shiftedProductDesc` to the `n`th coproduct summand recovers the `n`th
coordinate of the product element. -/
@[reassoc (attr := simp)]
theorem coproductInclusion_comp_shiftedProductDesc {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (L : D) (x : shiftedProduct K L) (n : ℕ) :
    P.coproductInclusion n ≫ shiftedProductDesc P L x =
      (Pi.π (shiftedTower K L).family n) x := sorry

/-- The underlying function from the product of shifted represented Hom groups to
`Hom_D(X, L)`: descend to the stored coproduct, move the shift to the source, then precompose
with the connecting morphism. -/
@[stacks 0CQX]
def shiftedProductMap {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D)
    (x : shiftedProduct K L) : X ⟶ L :=
  P.connecting ≫
    ShiftedHom.sourceShiftEquiv P.coproduct.cocone.pt L (-1 : ℤ)
      (shiftedProductDesc P L x)

/-- `shiftedProductMap` sends zero to zero. -/
theorem shiftedProductMap_zero {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D) :
    shiftedProductMap P L 0 = 0 := sorry

/-- `shiftedProductMap` preserves addition. -/
theorem shiftedProductMap_add {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D)
    (x y : shiftedProduct K L) :
    shiftedProductMap P L (x + y) = shiftedProductMap P L x + shiftedProductMap P L y := sorry

/-- The additive morphism from the product of shifted represented Hom groups to
`Hom_D(X, L)` before passage to the Milnor quotient. -/
@[stacks 0CQX]
def shiftedProductToHom {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D) :
    shiftedProduct K L ⟶ (preadditiveYoneda.obj L).obj (op X) :=
  AddCommGrpCat.ofHom
    { toFun := shiftedProductMap P L
      map_zero' := shiftedProductMap_zero P L
      map_add' := shiftedProductMap_add P L }

/-- Evaluating `shiftedProductToHom` is the explicit shifted-product construction. -/
@[simp]
theorem shiftedProductToHom_apply {K : ℕ ⥤ D} {X : D} (P : Presentation K X)
    (L : D) (x : shiftedProduct K L) :
    shiftedProductToHom P L x = shiftedProductMap P L x := sorry

/-- The shifted-product map annihilates the Milnor difference map. -/
@[reassoc, stacks 0CQX]
theorem difference_comp_shiftedProductToHom {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (L : D) :
    (shiftedTower K L).milnorDifferenceMap ≫ shiftedProductToHom P L = 0 := sorry

/-- The canonical inclusion of the first derived limit of shifted represented Hom groups into
`Hom_D(X, L)`. -/
@[stacks 0CQX]
def r1Inclusion {K : ℕ ⥤ D} {X : D} (P : Presentation K X) (L : D) :
    canonicalR1 (shiftedTower K L) ⟶ (preadditiveYoneda.obj L).obj (op X) :=
  canonicalR1.desc (shiftedTower K L) (shiftedProductToHom P L)
    (difference_comp_shiftedProductToHom P L)

/-- Composing the canonical Milnor quotient with `r1Inclusion` recovers the explicit map from
the shifted product. -/
@[reassoc (attr := simp), stacks 0CQX]
theorem quotient_comp_r1Inclusion {K : ℕ ⥤ D} {X : D} (P : Presentation K X)
    (L : D) :
    canonicalR1.π (shiftedTower K L) ≫ r1Inclusion P L = shiftedProductToHom P L := sorry

/-- The first-derived-limit inclusion followed by the map to the inverse limit is zero. -/
@[reassoc, stacks 0CQX]
theorem r1Inclusion_comp_homToLimit {K : ℕ ⥤ D} {X : D}
    (P : Presentation K X) (L : D) :
    r1Inclusion P L ≫ homToLimit P L = 0 := sorry

end CategoryTheory.HomotopyColimit.RepresentedHom

end
