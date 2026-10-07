module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Products.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Symmetric presentation of a categorical pullback

Comparison between the ordinary iso-comma model `F ⊡ G` and the symmetric diagonal model
`(F.prod G) ⊡ Functor.diag C`.
-/

@[expose] public section

namespace CategoryTheory.Limits

open CategoryTheory.Prod
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

noncomputable section

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

/- `CategoricalPullback` is the verified owner for both presentations: applied to `F.prod G`
and `Functor.diag C` it gives exactly the quintuple category, while applied to `F` and `G` it
gives the triple category from Example 4.31.3. `CategoricalPullback.functorEquiv` and
`CatCommSqOver.toFunctorToCategoricalPullback` construct the comparison from a square, but
mathlib has no equivalence theorem for this diagonal specialization. The square conversion is
therefore generalized only over its apex and input square; specializing it to the canonical
diagonal pullback square recovers the source functor and gives later items a reusable bridge. -/

/- Operations converting symmetric diagonal squares to ordinary pair squares. -/
namespace CategoricalPullback.CatCommSqOver.Symmetric

/-- Project a square over `F.prod G` and `Functor.diag C` to a square over `F` and `G`.
Objectwise, the two components of the structural isomorphism are combined as `a ≪≫ b.symm`. -/
def toPair (F : A ⥤ C) (G : B ⥤ C)
    {X : Type u₄} [Category.{v₄} X]
    (P : CatCommSqOver (F.prod G) (Functor.diag C) X) :
    CatCommSqOver F G X where
  fst := P.fst ⋙ CategoryTheory.Prod.fst A B
  snd := P.fst ⋙ CategoryTheory.Prod.snd A B
  iso :=
    (Functor.isoWhiskerRight P.iso (CategoryTheory.Prod.fst C C) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft P.snd (Functor.prod'CompFst (𝟭 C) (𝟭 C)) ≪≫
      Functor.rightUnitor _) ≪≫
    (Functor.isoWhiskerRight P.iso (CategoryTheory.Prod.snd C C) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft P.snd (Functor.prod'CompSnd (𝟭 C) (𝟭 C)) ≪≫
      Functor.rightUnitor _).symm

namespace toPair

/-- The first leg of the pair square is the first product projection of the symmetric leg. -/
@[simp]
theorem fst (F : A ⥤ C) (G : B ⥤ C)
    {X : Type u₄} [Category.{v₄} X]
    (P : CatCommSqOver (F.prod G) (Functor.diag C) X) :
    (toPair F G P).fst = P.fst ⋙ CategoryTheory.Prod.fst A B := sorry

/-- The second leg of the pair square is the second product projection of the symmetric leg. -/
@[simp]
theorem snd (F : A ⥤ C) (G : B ⥤ C)
    {X : Type u₄} [Category.{v₄} X]
    (P : CatCommSqOver (F.prod G) (Functor.diag C) X) :
    (toPair F G P).snd = P.fst ⋙ CategoryTheory.Prod.snd A B := sorry

/-- At an object, the pair-square structural isomorphism is the first projection of the
symmetric structural isomorphism followed by the inverse of its second projection. -/
@[simp]
theorem iso.app (F : A ⥤ C) (G : B ⥤ C)
    {X : Type u₄} [Category.{v₄} X]
    (P : CatCommSqOver (F.prod G) (Functor.diag C) X) (x : X) :
    (toPair F G P).iso.app x =
      (CategoryTheory.Prod.fst C C).mapIso (P.iso.app x) ≪≫
        ((CategoryTheory.Prod.snd C C).mapIso (P.iso.app x)).symm := sorry

/-- The forward structural map of the pair square is the first projected structural map
followed by the inverse second projected structural map. -/
@[simp]
theorem iso.hom.app (F : A ⥤ C) (G : B ⥤ C)
    {X : Type u₄} [Category.{v₄} X]
    (P : CatCommSqOver (F.prod G) (Functor.diag C) X) (x : X) :
    (toPair F G P).iso.hom.app x =
      ((CategoryTheory.Prod.fst C C).mapIso (P.iso.app x)).hom ≫
        ((CategoryTheory.Prod.snd C C).mapIso (P.iso.app x)).inv := sorry

/-- The inverse structural map of the pair square is the second projected structural map
followed by the inverse first projected structural map. -/
@[simp]
theorem iso.inv.app (F : A ⥤ C) (G : B ⥤ C)
    {X : Type u₄} [Category.{v₄} X]
    (P : CatCommSqOver (F.prod G) (Functor.diag C) X) (x : X) :
    (toPair F G P).iso.inv.app x =
      ((CategoryTheory.Prod.snd C C).mapIso (P.iso.app x)).hom ≫
        ((CategoryTheory.Prod.fst C C).mapIso (P.iso.app x)).inv := sorry

end toPair

end CategoricalPullback.CatCommSqOver.Symmetric

/- Symmetries between the ordinary and diagonal presentations of categorical pullbacks. -/
namespace CategoricalPullback.Symmetric

/-- The canonical comparison from the symmetric quintuple model
`(F.prod G) ⊡ (Functor.diag C)` to the triple model `F ⊡ G`. On objects it sends
`(A, B, C, a, b)` to `(A, B, a ≪≫ b.symm)`, i.e. to `(A, B, b⁻¹ ∘ a)`. -/
def comparison (F : A ⥤ C) (G : B ⥤ C) :
    (F.prod G) ⊡ (Functor.diag C) ⥤ F ⊡ G :=
  (toFunctorToCategoricalPullback F G _).obj
    (CatCommSqOver.Symmetric.toPair F G
      ((toCatCommSqOver (F.prod G) (Functor.diag C) _).obj (𝟭 _)))

namespace comparison

/-- The first object selected by the symmetric comparison is the first entry of the product
object. -/
@[simp]
theorem obj.fst (F : A ⥤ C) (G : B ⥤ C)
    (x : (F.prod G) ⊡ (Functor.diag C)) :
    ((comparison F G).obj x).fst = x.fst.fst := sorry

/-- The second object selected by the symmetric comparison is the second entry of the product
object. -/
@[simp]
theorem obj.snd (F : A ⥤ C) (G : B ⥤ C)
    (x : (F.prod G) ⊡ (Functor.diag C)) :
    ((comparison F G).obj x).snd = x.fst.snd := sorry

/-- The structural isomorphism selected by the symmetric comparison is the first projection of
the symmetric structural isomorphism followed by the inverse of its second projection. -/
@[simp]
theorem obj.iso (F : A ⥤ C) (G : B ⥤ C)
    (x : (F.prod G) ⊡ (Functor.diag C)) :
    ((comparison F G).obj x).iso =
      (CategoryTheory.Prod.fst C C).mapIso x.iso ≪≫
        ((CategoryTheory.Prod.snd C C).mapIso x.iso).symm := sorry

/-- The forward structural map selected by the symmetric comparison is the first projected map
followed by the inverse second projected map. -/
@[simp]
theorem obj.iso.hom (F : A ⥤ C) (G : B ⥤ C)
    (x : (F.prod G) ⊡ (Functor.diag C)) :
    ((comparison F G).obj x).iso.hom =
      ((CategoryTheory.Prod.fst C C).mapIso x.iso).hom ≫
        ((CategoryTheory.Prod.snd C C).mapIso x.iso).inv := sorry

/-- The inverse structural map selected by the symmetric comparison is the second projected map
followed by the inverse first projected map. -/
@[simp]
theorem obj.iso.inv (F : A ⥤ C) (G : B ⥤ C)
    (x : (F.prod G) ⊡ (Functor.diag C)) :
    ((comparison F G).obj x).iso.inv =
      ((CategoryTheory.Prod.snd C C).mapIso x.iso).hom ≫
        ((CategoryTheory.Prod.fst C C).mapIso x.iso).inv := sorry

/-- On morphisms, the symmetric comparison retains the first component of the product map. -/
@[simp]
theorem map.fst (F : A ⥤ C) (G : B ⥤ C)
    {x y : (F.prod G) ⊡ (Functor.diag C)} (f : x ⟶ y) :
    ((comparison F G).map f).fst = f.fst.fst := sorry

/-- On morphisms, the symmetric comparison retains the second component of the product map. -/
@[simp]
theorem map.snd (F : A ⥤ C) (G : B ⥤ C)
    {x y : (F.prod G) ⊡ (Functor.diag C)} (f : x ⟶ y) :
    ((comparison F G).map f).snd = f.fst.snd := sorry

/-- The functor sending a symmetric quintuple
`(A, B, C, a, b)` to `(A, B, b⁻¹ ∘ a)` is an equivalence from
`(F.prod G) ⊡ (Functor.diag C)` to the `2`-fibre-product category `F ⊡ G` of
Example 4.31.3. -/
@[stacks 06RL]
instance isEquivalence
    (F : A ⥤ C) (G : B ⥤ C) :
    (comparison F G).IsEquivalence := sorry
/- Proof strategy: construct the quasi-inverse with
`CatCommSqOver.toFunctorToCategoricalPullback`, sending `(A, B, c)` to
`(A, B, G.obj B, c, Iso.refl _)`. Use `CategoricalPullback.mkNatIso` to build the unit and
counit from `CategoryTheory.prod.etaIso`, the source structural isomorphism, and identity
isomorphisms; their compatibility reduces to `CategoricalPullback.Hom.w` and the two inverse
laws for the source isomorphism. Package these data with `Functor.IsEquivalence.mk'`; the category
hypotheses on `A`, `B`, and `C` discharge all assumptions of those APIs. -/

end comparison

end CategoricalPullback.Symmetric

end

end CategoryTheory.Limits
