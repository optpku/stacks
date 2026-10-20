module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

@[expose] public section

/-!
# Product slices: basic constructions

This module owns the explicit functors between the categorical pullback of two slice
projections and the slice over the product.  The equivalence and its computation API are
layered in `ProductSlice.Equivalence` and `ProductSlice.Computations`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

universe v u

namespace CategoryTheory

namespace Limits.CategoricalPullback.ProductSlice

section Basic

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]

namespace Implementation

/- The map compatibility equations are kept private because the public specification is the
   functor itself and its componentwise readouts in `ProductSlice.Computations`. -/

/-- Compatibility needed to map a morphism of the categorical pullback to the product slice. -/
private theorem toProduct_map_comm (U V : C)
    {x y : (Over.forget U) ⊡ (Over.forget V)} (f : x ⟶ y) :
    f.fst.left ≫ Limits.prod.lift y.fst.hom (y.iso.hom ≫ y.snd.hom) =
      Limits.prod.lift x.fst.hom (x.iso.hom ≫ x.snd.hom) := sorry
/- Proof strategy: use `Limits.prod.hom_ext`; the first projection is `Over.w f.fst`, while the
second combines `f.w` with `Over.w f.snd`. -/

end Implementation

/-- Forward functor of the product-of-slices equivalence: package the two slice arrows and the
structural isomorphism into a single arrow to `U ⨯ V`. -/
noncomputable def toProduct (U V : C) :
    (Over.forget U) ⊡ (Over.forget V) ⥤ Over (Limits.prod U V) where
  obj x := Over.mk (Limits.prod.lift x.fst.hom (x.iso.hom ≫ x.snd.hom))
  map {x y} f := Over.homMk f.fst.left (Implementation.toProduct_map_comm U V f)

namespace Implementation

/-- Compatibility of the first projected slice morphism with its structure map. -/
private theorem fromProduct_fst_comm (U V : C)
    {c d : Over (Limits.prod U V)} (g : c ⟶ d) :
    g.left ≫ (d.hom ≫ Limits.prod.fst) = c.hom ≫ Limits.prod.fst := sorry
/- Proof strategy: reassociate `Over.w g` and postcompose it with `Limits.prod.fst`. -/

/-- Compatibility of the second projected slice morphism with its structure map. -/
private theorem fromProduct_snd_comm (U V : C)
    {c d : Over (Limits.prod U V)} (g : c ⟶ d) :
    g.left ≫ (d.hom ≫ Limits.prod.snd) = c.hom ≫ Limits.prod.snd := sorry
/- Proof strategy: reassociate `Over.w g` and postcompose it with `Limits.prod.snd`. -/

/-- Compatibility of the two projected slice morphisms with the identity structural isomorphisms. -/
private theorem fromProduct_map_comm (U V : C)
    {c d : Over (Limits.prod U V)} (g : c ⟶ d) :
    g.left ≫ 𝟙 d.left = 𝟙 c.left ≫ g.left := sorry
/- Proof strategy: both sides reduce to `g.left` by the unit laws. -/

end Implementation

/-- Inverse functor of the product-of-slices equivalence: a slice over `U ⨯ V` projects to its two
factors with the identity structural isomorphism. -/
noncomputable def fromProduct (U V : C) :
    Over (Limits.prod U V) ⥤ (Over.forget U) ⊡ (Over.forget V) where
  obj c :=
    { fst := Over.mk (c.hom ≫ Limits.prod.fst)
      snd := Over.mk (c.hom ≫ Limits.prod.snd)
      iso := Iso.refl c.left }
  map {c d} g :=
    { fst := Over.homMk g.left (Implementation.fromProduct_fst_comm U V g)
      snd := Over.homMk g.left (Implementation.fromProduct_snd_comm U V g)
      w := Implementation.fromProduct_map_comm U V g }

end Basic

end Limits.CategoricalPullback.ProductSlice

end CategoryTheory
