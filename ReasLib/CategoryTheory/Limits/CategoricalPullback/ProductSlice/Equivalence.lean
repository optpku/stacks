module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.Basic

@[expose] public section

/-!
# Product slices: equivalence

This module owns the unit, counit, and triangle data for the canonical equivalence between the
categorical pullback of slice projections and the slice over a product.  Component formulas are
kept in `ProductSlice.Computations`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

universe v u

namespace CategoryTheory

namespace Limits.CategoricalPullback.ProductSlice

section Equivalence

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]

namespace Implementation

/-- Compatibility of the first slice component of the product-of-slices unit. -/
private theorem Equivalence.unitFst_comm (U V : C) (x : (Over.forget U) ⊡ (Over.forget V)) :
    (Iso.refl x.fst.left).hom ≫
        ((toProduct U V ⋙ fromProduct U V).obj x).fst.hom =
      x.fst.hom := sorry
/- Proof strategy: unfold the two functors and use `Limits.prod.lift_fst`. -/

/-- First slice component of the product-of-slices unit. -/
private noncomputable def Equivalence.unitFstIso (U V : C)
    (x : (Over.forget U) ⊡ (Over.forget V)) :
    x.fst ≅ ((toProduct U V ⋙ fromProduct U V).obj x).fst :=
  Over.isoMk (Iso.refl x.fst.left) (Equivalence.unitFst_comm U V x)

/-- Compatibility of the second slice component of the product-of-slices unit. -/
private theorem Equivalence.unitSnd_comm (U V : C) (x : (Over.forget U) ⊡ (Over.forget V)) :
    x.iso.symm.hom ≫
        ((toProduct U V ⋙ fromProduct U V).obj x).snd.hom =
      x.snd.hom := sorry
/- Proof strategy: unfold the two functors, use `Limits.prod.lift_snd`, and cancel
`x.iso.inv ≫ x.iso.hom`. -/

/-- Second slice component of the product-of-slices unit. -/
private noncomputable def Equivalence.unitSndIso (U V : C)
    (x : (Over.forget U) ⊡ (Over.forget V)) :
    x.snd ≅ ((toProduct U V ⋙ fromProduct U V).obj x).snd :=
  Over.isoMk x.iso.symm (Equivalence.unitSnd_comm U V x)

/-- Compatibility of the two slice components with the pullback structural isomorphism. -/
private theorem Equivalence.unitComponent_comm (U V : C)
    (x : (Over.forget U) ⊡ (Over.forget V)) :
    (Over.forget U).map (Equivalence.unitFstIso U V x).hom ≫
        ((toProduct U V ⋙ fromProduct U V).obj x).iso.hom =
      x.iso.hom ≫ (Over.forget V).map (Equivalence.unitSndIso U V x).hom := sorry
/- Proof strategy: unfold the component isomorphisms; both sides reduce to the identity on
`x.fst.left` using the inverse-hom identity of `x.iso`. -/

/-- Objectwise unit isomorphism for the product-of-slices equivalence. -/
private noncomputable def Equivalence.unitComponent (U V : C)
    (x : (Over.forget U) ⊡ (Over.forget V)) :
    x ≅ (toProduct U V ⋙ fromProduct U V).obj x :=
  CategoricalPullback.mkIso (Equivalence.unitFstIso U V x)
    (Equivalence.unitSndIso U V x) (Equivalence.unitComponent_comm U V x)

/-- Naturality of the product-of-slices unit components. -/
private theorem Equivalence.unitNaturality (U V : C)
    {x y : (Over.forget U) ⊡ (Over.forget V)} (f : x ⟶ y) :
    f ≫ (Equivalence.unitComponent U V y).hom =
      (Equivalence.unitComponent U V x).hom ≫
        (toProduct U V ⋙ fromProduct U V).map f := sorry
/- Proof strategy: apply `CategoricalPullback.hom_ext` and then `Over.OverMorphism.ext`; the first
projection is immediate and the second is `CategoricalPullback.Hom.w' f`. -/

/-- Unit natural isomorphism for the product-of-slices equivalence. -/
private noncomputable def Equivalence.unitIso (U V : C) :
    𝟭 ((Over.forget U) ⊡ (Over.forget V)) ≅
      toProduct U V ⋙ fromProduct U V :=
  NatIso.ofComponents (Equivalence.unitComponent U V)
    (Equivalence.unitNaturality U V)

/-- Compatibility of the counit component with the product-slice structure map. -/
private theorem Equivalence.counit_comm (U V : C) (c : Over (Limits.prod U V)) :
    (Iso.refl c.left).hom ≫ c.hom =
      ((fromProduct U V ⋙ toProduct U V).obj c).hom := sorry
/- Proof strategy: unfold both functors and use the product extensionality identity
`Limits.prod.lift (c.hom ≫ fst) (c.hom ≫ snd) = c.hom`. -/

/-- Objectwise counit isomorphism for the product-slices equivalence. -/
private noncomputable def Equivalence.counitComponent (U V : C) (c : Over (Limits.prod U V)) :
    (fromProduct U V ⋙ toProduct U V).obj c ≅ c :=
  Over.isoMk (Iso.refl c.left) (Equivalence.counit_comm U V c)

/-- Naturality of the product-slices counit components. -/
private theorem Equivalence.counitNaturality (U V : C)
    {c d : Over (Limits.prod U V)} (g : c ⟶ d) :
    (fromProduct U V ⋙ toProduct U V).map g ≫
        (Equivalence.counitComponent U V d).hom =
      (Equivalence.counitComponent U V c).hom ≫ g := sorry
/- Proof strategy: apply `Over.OverMorphism.ext`; both sides have underlying morphism `g.left`. -/

/-- Counit natural isomorphism for the product-slices equivalence. -/
private noncomputable def Equivalence.counitIso (U V : C) :
    fromProduct U V ⋙ toProduct U V ≅ 𝟭 (Over (Limits.prod U V)) :=
  NatIso.ofComponents (Equivalence.counitComponent U V)
    (Equivalence.counitNaturality U V)

/-- Triangle coherence for the product-of-slices equivalence. -/
private theorem Equivalence.triangle (U V : C)
    (x : (Over.forget U) ⊡ (Over.forget V)) :
    (toProduct U V).map ((Equivalence.unitIso U V).hom.app x) ≫
        (Equivalence.counitIso U V).hom.app ((toProduct U V).obj x) =
      𝟙 ((toProduct U V).obj x) := sorry
/- Proof strategy: apply `Over.OverMorphism.ext`; the underlying morphism is the identity. -/

end Implementation

/- The canonical equivalence is assembled from the two explicit functors and the single unit,
   counit, and triangle package above. -/

/-- The product-of-slices equivalence `C/U ×_C C/V ≅ C/(U ⨯ V)` in categorical-pullback form. -/
noncomputable def equivalence (U V : C) :
    (Over.forget U) ⊡ (Over.forget V) ≌ Over (Limits.prod U V) where
  functor := toProduct U V
  inverse := fromProduct U V
  unitIso := Implementation.Equivalence.unitIso U V
  counitIso := Implementation.Equivalence.counitIso U V
  functor_unitIso_comp := Implementation.Equivalence.triangle U V

end Equivalence

end Limits.CategoricalPullback.ProductSlice

end CategoryTheory
