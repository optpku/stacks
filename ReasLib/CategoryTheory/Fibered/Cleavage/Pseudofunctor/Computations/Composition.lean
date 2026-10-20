module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Construction

@[expose] public section

/-!
# Composition comparison of the pseudofunctor associated to a cleavage

The bicategorical composition constraint is normalized to the intrinsic reindexing comparison,
including the flexible form over a specified composite and its cartesian factorization API.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor.Cleavage

variable {p : S ⥤ C} (χ : p.Cleavage)

/-- After forgetting the `Cat` wrapper, the base-facing composition comparison is the intrinsic
composition comparison of the cleavage. -/
@[simp]
theorem toPseudofunctor.mapCompOp.toNatIso
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    Cat.Hom.toNatIso (χ.toPseudofunctor.mapCompOp f g) =
      Reindex.compIso χ f g := sorry

/-- At an actual composite `g ≫ f`, the hom component of `mapCompOp` is the canonical
cleavage comparison component. This is the normalization theorem from the bicategorical
presentation to the intrinsic reindexing API. -/
@[simp]
theorem toPseudofunctor.mapCompOp.hom.app
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    (χ.toPseudofunctor.mapCompOp f g).hom.toNatTrans.app x =
      (Reindex.compIsoApp χ f g x).hom := sorry
/- Proof strategy: unfold `mapCompOp` and `toPseudofunctor`, then normalize
`Pseudofunctor.mapComp'` at the canonical composite. -/

/-- At an actual composite `g ≫ f`, the inverse component of `mapCompOp` is the inverse
canonical cleavage comparison component. -/
@[simp]
theorem toPseudofunctor.mapCompOp.inv.app
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    (χ.toPseudofunctor.mapCompOp f g).inv.toNatTrans.app x =
      (Reindex.compIsoApp χ f g x).inv := sorry
/- Proof strategy: use the same normalization as the hom component and take the inverse side of
the resulting natural isomorphism. -/

/-- After forgetting the `Cat` wrapper, mathlib's standard composition comparison is the
intrinsic composition comparison of the cleavage. -/
@[simp]
theorem toPseudofunctor.mapComp.toNatIso
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    Cat.Hom.toNatIso
        (χ.toPseudofunctor.mapComp f.op.toLoc g.op.toLoc) =
      Reindex.compIso χ f g := sorry

/-- The hom component of mathlib's standard composition comparison is the intrinsic cleavage
composition component. -/
@[simp]
theorem toPseudofunctor.mapComp.hom.app
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    (χ.toPseudofunctor.mapComp f.op.toLoc g.op.toLoc).hom.toNatTrans.app x =
      (Reindex.compIsoApp χ f g x).hom := sorry

/-- The inverse component of mathlib's standard composition comparison is the inverse intrinsic
cleavage composition component. -/
@[simp]
theorem toPseudofunctor.mapComp.inv.app
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V) (x : Fiber p U) :
    (χ.toPseudofunctor.mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app x =
      (Reindex.compIsoApp χ f g x).inv := sorry

/-- Over a specified composite, the forward pseudofunctor comparison component is the intrinsic
specified-composite reindexing comparison. -/
@[simp]
theorem toPseudofunctor.mapCompOp'.hom.app
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : Fiber p D) :
    (χ.toPseudofunctor.mapCompOp' f g gf hgf).hom.toNatTrans.app x =
      (Reindex.specifiedCompIsoApp χ f g gf hgf x).hom := sorry

/-- Over a specified composite, the inverse pseudofunctor comparison component is the inverse
intrinsic specified-composite reindexing comparison. -/
@[simp]
theorem toPseudofunctor.mapCompOp'.inv.app
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D)
    (hgf : g ≫ f = gf) (x : Fiber p D) :
    (χ.toPseudofunctor.mapCompOp' f g gf hgf).inv.toNatTrans.app x =
      (Reindex.specifiedCompIsoApp χ f g gf hgf x).inv := sorry

/-- The hom component of the base-facing composition comparison factors the iterated chosen
cartesian arrows through the chosen arrow over the specified composite. -/
@[reassoc]
theorem toPseudofunctor.mapCompOp'.hom.app.fac
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (x : Fiber p D) :
    ((χ.toPseudofunctor.mapCompOp' f g gf hgf).hom.toNatTrans.app x).1 ≫
        χ.cartesianHom g ((χ.reindex f).obj x) ≫
        χ.cartesianHom f x =
      χ.cartesianHom gf x := sorry
/- Proof strategy: eliminate `hgf`, reduce `mapCompOp'` to the cleavage composition comparison,
and apply `Reindex.specifiedCompIsoApp.hom.fac`. -/

/-- The inverse component of the base-facing composition comparison factors the chosen arrow over
the specified composite through the iterated chosen cartesian arrows. -/
@[reassoc]
theorem toPseudofunctor.mapCompOp'.inv.app.fac
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf)
    (x : Fiber p D) :
    ((χ.toPseudofunctor.mapCompOp' f g gf hgf).inv.toNatTrans.app x).1 ≫
        χ.cartesianHom gf x =
      χ.cartesianHom g ((χ.reindex f).obj x) ≫
        χ.cartesianHom f x := sorry
/- Proof strategy: eliminate `hgf`, reduce `mapCompOp'` to the inverse cleavage comparison,
and apply `Reindex.specifiedCompIsoApp.inv.fac`. -/

end Functor.Cleavage

end CategoryTheory
