module

public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Intrinsic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Reindex.Explicit.Construction.Composition
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

/-!
# Nested restriction comparison of fibrewise 2-fibre products

A commuting square in the base of a pair of morphisms of categories fibred in
groupoids induces a 2-commutative square of fibrewise 2-fibre products. The
induced comparison functor is `fibreProductRestrictionComparison`.
-/

@[expose] public section

open CategoryTheory Limits CategoricalPullback
open scoped CategoricalPullback

universe u v w vS

namespace CategoryTheory.FiberedCategoryOver.Groupoids

variable {C : Type u} [Category.{v} C]

/-- Reindexing of a fibrewise 2-fibre product of groupoid-fibred morphisms along
a morphism of the base. -/
noncomputable def fibreProductReindex
    {𝒳 𝒴 𝒵 : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴) {U V : C} (f : V ⟶ U) :
    (fiberFunctor p U) ⊡ (fiberFunctor q U) ⥤
      (fiberFunctor p V) ⊡ (fiberFunctor q V) :=
  BasedCategory.PseudoPullback.reindex.explicit.functor
    (toCartesianBasedFunctor p) (toCartesianBasedFunctor q)
    (Functor.Cleavage.ofIsFibered 𝒳.p) (Functor.Cleavage.ofIsFibered 𝒵.p)
    (Functor.Cleavage.ofIsFibered 𝒴.p) f

/-- `fibreProductReindex` is explicit-cleavage reindexing of the two fibre functors. -/
theorem fibreProductReindex.eqExplicit
    {𝒳 𝒴 𝒵 : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴) {U V : C} (f : V ⟶ U) :
    fibreProductReindex p q f =
      BasedCategory.PseudoPullback.reindex.explicit.functor
        (toCartesianBasedFunctor p) (toCartesianBasedFunctor q)
        (Functor.Cleavage.ofIsFibered 𝒳.p) (Functor.Cleavage.ofIsFibered 𝒵.p)
        (Functor.Cleavage.ofIsFibered 𝒴.p) f := sorry

/-- Direct and successive fibrewise 2-fibre-product reindexing are naturally isomorphic. -/
noncomputable def fibreProductReindex.compIso
    {𝒳 𝒴 𝒵 : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴) {U V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    fibreProductReindex p q (g ≫ f) ≅
      fibreProductReindex p q f ⋙ fibreProductReindex p q g :=
  BasedCategory.PseudoPullback.reindex.explicit.mapCompIso
    (toCartesianBasedFunctor p) (toCartesianBasedFunctor q)
    (Functor.Cleavage.ofIsFibered 𝒳.p) (Functor.Cleavage.ofIsFibered 𝒵.p)
    (Functor.Cleavage.ofIsFibered 𝒴.p) f g

/-- Equal base arrows induce naturally isomorphic fibrewise 2-fibre-product reindexings. -/
noncomputable def fibreProductReindex.congrIso
    {𝒳 𝒴 𝒵 : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴) {U V : C} {f g : V ⟶ U} (h : f = g) :
    fibreProductReindex p q f ≅ fibreProductReindex p q g :=
  eqToIso (congrArg (fibreProductReindex p q) h)

/-- The 2-commutative square of fibrewise 2-fibre products obtained by restricting along a
commuting square in the base. -/
noncomputable def fibreProductRestrictionSquare
    {𝒳 𝒴 𝒵 : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) :
    CatCommSqOver (fibreProductReindex p q toY) (fibreProductReindex p q toX')
      ((fiberFunctor p Y') ⊡ (fiberFunctor q Y')) where
  fst := fibreProductReindex p q fromY
  snd := fibreProductReindex p q fromX'
  iso :=
    (fibreProductReindex.compIso p q fromY toY).symm ≪≫
      fibreProductReindex.congrIso p q hw.symm ≪≫
      fibreProductReindex.compIso p q fromX' toX'

/-- The first leg of `fibreProductRestrictionSquare` is reindexing along `fromY`. -/
@[simp]
theorem fibreProductRestrictionSquare_fst
    {𝒳 𝒴 𝒵 : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) :
    (fibreProductRestrictionSquare p q hw).fst = fibreProductReindex p q fromY := sorry

/-- The second leg of `fibreProductRestrictionSquare` is reindexing along `fromX'`. -/
@[simp]
theorem fibreProductRestrictionSquare_snd
    {𝒳 𝒴 𝒵 : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) :
    (fibreProductRestrictionSquare p q hw).snd = fibreProductReindex p q fromX' := sorry

/-- The comparison functor from the fibrewise 2-fibre product over `Y'` into the 2-fibre
product of the restrictions along `X ⟶ Y` and `X ⟶ X'`. -/
noncomputable def fibreProductRestrictionComparison
    {𝒳 𝒴 𝒵 : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) :
    (fiberFunctor p Y') ⊡ (fiberFunctor q Y') ⥤
      (fibreProductReindex p q toY) ⊡ (fibreProductReindex p q toX') :=
  (fibreProductRestrictionSquare p q hw).comparison

/-- The first projection of `fibreProductRestrictionComparison` on objects is reindexing
along `fromY`. -/
@[simp]
theorem fibreProductRestrictionComparison_obj_fst
    {𝒳 𝒴 𝒵 : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY)
    (t : (fiberFunctor p Y') ⊡ (fiberFunctor q Y')) :
    ((fibreProductRestrictionComparison p q hw).obj t).fst =
      (fibreProductReindex p q fromY).obj t := sorry

/-- The second projection of `fibreProductRestrictionComparison` on objects is reindexing
along `fromX'`. -/
@[simp]
theorem fibreProductRestrictionComparison_obj_snd
    {𝒳 𝒴 𝒵 : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY)
    (t : (fiberFunctor p Y') ⊡ (fiberFunctor q Y')) :
    ((fibreProductRestrictionComparison p q hw).obj t).snd =
      (fibreProductReindex p q fromX').obj t := sorry

/-- The structural isomorphism of `fibreProductRestrictionComparison` on objects is the
square's 2-cell. -/
@[simp]
theorem fibreProductRestrictionComparison_obj_iso
    {𝒳 𝒴 𝒵 : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY)
    (t : (fiberFunctor p Y') ⊡ (fiberFunctor q Y')) :
    ((fibreProductRestrictionComparison p q hw).obj t).iso =
      (fibreProductRestrictionSquare p q hw).iso.app t := sorry

/-- Objects of `fibreProductRestrictionComparison` record the two fibrewise reindexings and
the structural 2-cell. -/
theorem fibreProductRestrictionComparison_spec
    {𝒳 𝒴 𝒵 : FiberedCategoryOver.Groupoids.{u, v, w, vS} C}
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)
    {X X' Y Y' : C} {toX' : X ⟶ X'} {toY : X ⟶ Y} {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY)
    (t : (fiberFunctor p Y') ⊡ (fiberFunctor q Y')) :
    ((fibreProductRestrictionComparison p q hw).obj t).fst =
      (fibreProductReindex p q fromY).obj t ∧
      ((fibreProductRestrictionComparison p q hw).obj t).snd =
        (fibreProductReindex p q fromX').obj t ∧
      ((fibreProductRestrictionComparison p q hw).obj t).iso =
        (fibreProductRestrictionSquare p q hw).iso.app t := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids
