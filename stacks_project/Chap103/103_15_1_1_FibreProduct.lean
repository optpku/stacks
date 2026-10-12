/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import stacks_project.Chap96.«96_5_0_1»
public import stacks_project.Chap103.«103_15_1_1_Map»

/-!
# Primed Yoneda 2-fibre products

For a 1-morphism `f : X ⟶ Y` of algebraic stacks and a lisse (resp. flat) object
`y` of `Y`, the primed 2-fibre product `(V ×_{y,Y} X)'` is the full subcategory
of `yonedaFibreProduct f ⟨y.obj, rfl⟩` on objects whose projection to `X` is
lisse (resp. flat). The restricted projection `pr'` lands in the lisse-étale
(resp. flat-fppf) site of `X`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids Limits Opposite
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- The object property on the Yoneda 2-fibre product selecting objects whose
projection to `X` is lisse. -/
def lisseYonedaFibreProduct.prop (f : X ⟶ Y) (y : lisseEtaleSite Y) :
    ObjectProperty (yonedaFibreProduct f ⟨y.obj, rfl⟩).total :=
  fun q ↦ isLisse X ((toFunctor (yonedaFibreProduct.pr f ⟨y.obj, rfl⟩)).obj q)

/-- The primed 2-fibre product `(V ×_{y,Y} X)'` of a lisse object `y` of `Y`. -/
abbrev lisseYonedaFibreProduct (f : X ⟶ Y) (y : lisseEtaleSite Y) :=
  (lisseYonedaFibreProduct.prop f y).FullSubcategory

/-- The object property on the Yoneda 2-fibre product selecting objects whose
projection to `X` is flat. -/
def flatYonedaFibreProduct.prop (f : X ⟶ Y) (y : flatFppfSite Y) :
    ObjectProperty (yonedaFibreProduct f ⟨y.obj, rfl⟩).total :=
  fun q ↦ isFlat X ((toFunctor (yonedaFibreProduct.pr f ⟨y.obj, rfl⟩)).obj q)

/-- The primed 2-fibre product `(V ×_{y,Y} X)'` of a flat object `y` of `Y`. -/
abbrev flatYonedaFibreProduct (f : X ⟶ Y) (y : flatFppfSite Y) :=
  (flatYonedaFibreProduct.prop f y).FullSubcategory

/-- Pack an object of the Yoneda 2-fibre product whose projection to `X` is
lisse as an object of `(V ×_{y,Y} X)'`. -/
def lisseYonedaFibreProduct.mk (f : X ⟶ Y) (y : lisseEtaleSite Y)
    {q : (yonedaFibreProduct f ⟨y.obj, rfl⟩).total}
    (hq : lisseYonedaFibreProduct.prop f y q) :
    lisseYonedaFibreProduct f y :=
  ⟨q, hq⟩

/-- The underlying object of `lisseYonedaFibreProduct.mk hq` is `q`. -/
theorem lisseYonedaFibreProduct.mk_obj (f : X ⟶ Y) (y : lisseEtaleSite Y)
    {q : (yonedaFibreProduct f ⟨y.obj, rfl⟩).total}
    (hq : lisseYonedaFibreProduct.prop f y q) :
    (lisseYonedaFibreProduct.mk f y hq).obj = q :=
  sorry

/-- Membership in `(V ×_{y,Y} X)'` is lisseness of the projection to `X`. -/
theorem lisseYonedaFibreProduct.mem_iff (f : X ⟶ Y) (y : lisseEtaleSite Y)
    (q : (yonedaFibreProduct f ⟨y.obj, rfl⟩).total) :
    lisseYonedaFibreProduct.prop f y q ↔
      isLisse X ((toFunctor (yonedaFibreProduct.pr f ⟨y.obj, rfl⟩)).obj q) :=
  sorry

/-- Pack an object of the Yoneda 2-fibre product whose projection to `X` is
flat as an object of `(V ×_{y,Y} X)'`. -/
def flatYonedaFibreProduct.mk (f : X ⟶ Y) (y : flatFppfSite Y)
    {q : (yonedaFibreProduct f ⟨y.obj, rfl⟩).total}
    (hq : flatYonedaFibreProduct.prop f y q) :
    flatYonedaFibreProduct f y :=
  ⟨q, hq⟩

/-- The underlying object of `flatYonedaFibreProduct.mk hq` is `q`. -/
theorem flatYonedaFibreProduct.mk_obj (f : X ⟶ Y) (y : flatFppfSite Y)
    {q : (yonedaFibreProduct f ⟨y.obj, rfl⟩).total}
    (hq : flatYonedaFibreProduct.prop f y q) :
    (flatYonedaFibreProduct.mk f y hq).obj = q :=
  sorry

/-- Membership in the flat primed 2-fibre product is flatness of the projection
to `X`. -/
theorem flatYonedaFibreProduct.mem_iff (f : X ⟶ Y) (y : flatFppfSite Y)
    (q : (yonedaFibreProduct f ⟨y.obj, rfl⟩).total) :
    flatYonedaFibreProduct.prop f y q ↔
      isFlat X ((toFunctor (yonedaFibreProduct.pr f ⟨y.obj, rfl⟩)).obj q) :=
  sorry

/-- The restricted projection `pr' : (V ×_{y,Y} X)' ⟶ X_{lisse,étale}`. -/
def lisseYonedaFibreProduct.pr (f : X ⟶ Y) (y : lisseEtaleSite Y) :
    lisseYonedaFibreProduct f y ⥤ lisseEtaleSite X :=
  (isLisse X).lift
    ((lisseYonedaFibreProduct.prop f y).ι ⋙
      toFunctor (yonedaFibreProduct.pr f ⟨y.obj, rfl⟩))
    fun q ↦ q.property

/-- The restricted projection `pr' : (V ×_{y,Y} X)' ⟶ X_{flat,fppf}`. -/
def flatYonedaFibreProduct.pr (f : X ⟶ Y) (y : flatFppfSite Y) :
    flatYonedaFibreProduct f y ⥤ flatFppfSite X :=
  (isFlat X).lift
    ((flatYonedaFibreProduct.prop f y).ι ⋙
      toFunctor (yonedaFibreProduct.pr f ⟨y.obj, rfl⟩))
    fun q ↦ q.property

/-- Composing `pr'` with the lisse-étale inclusion recovers the Yoneda
projection on the ambient 2-fibre product. -/
def lisseYonedaFibreProduct.pr_comp_ι (f : X ⟶ Y) (y : lisseEtaleSite Y) :
    lisseYonedaFibreProduct.pr f y ⋙ lisseEtaleInclusion X ≅
      (lisseYonedaFibreProduct.prop f y).ι ⋙
        toFunctor (yonedaFibreProduct.pr f ⟨y.obj, rfl⟩) :=
  (isLisse X).liftCompιIso
    ((lisseYonedaFibreProduct.prop f y).ι ⋙
      toFunctor (yonedaFibreProduct.pr f ⟨y.obj, rfl⟩))
    fun q ↦ q.property

/-- Composing `pr'` with the flat-fppf inclusion recovers the Yoneda projection
on the ambient 2-fibre product. -/
def flatYonedaFibreProduct.pr_comp_ι (f : X ⟶ Y) (y : flatFppfSite Y) :
    flatYonedaFibreProduct.pr f y ⋙ flatFppfInclusion X ≅
      (flatYonedaFibreProduct.prop f y).ι ⋙
        toFunctor (yonedaFibreProduct.pr f ⟨y.obj, rfl⟩) :=
  (isFlat X).liftCompιIso
    ((flatYonedaFibreProduct.prop f y).ι ⋙
      toFunctor (yonedaFibreProduct.pr f ⟨y.obj, rfl⟩))
    fun q ↦ q.property

/-- The morphism `f'(pr'(q)) ⟶ y` in the lisse-étale site of `Y` encoded by an
object of `(V ×_{y,Y} X)'`. -/
def lisseYonedaFibreProduct.arrow (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y)
    (q : lisseYonedaFibreProduct f y) :
    (lisseEtaleMap f).obj ((lisseYonedaFibreProduct.pr f y).obj q) ⟶ y :=
  homMk (yonedaFibreProduct.arrow f ⟨y.obj, rfl⟩ q.obj)

/-- The morphism `f'(pr'(q)) ⟶ y` in the flat-fppf site of `Y` encoded by an
object of `(V ×_{y,Y} X)'`. -/
def flatYonedaFibreProduct.arrow (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y)
    (q : flatYonedaFibreProduct f y) :
    (flatFppfMap f).obj ((flatYonedaFibreProduct.pr f y).obj q) ⟶ y :=
  homMk (yonedaFibreProduct.arrow f ⟨y.obj, rfl⟩ q.obj)


/-- The functor sending an object of `(V ×_{y,Y} X)'` to the corresponding
structured arrow `f'(pr'(q)) ⟶ y`. -/
def lisseYonedaFibreProduct.toStructuredArrow (f : X ⟶ Y) [Smooth f]
    (y : lisseEtaleSite Y) :
    (lisseYonedaFibreProduct f y)ᵒᵖ ⥤
      StructuredArrow (op y) (lisseEtaleMap f).op where
  obj q := StructuredArrow.mk (op (lisseYonedaFibreProduct.arrow f y q.unop))
  map {q q'} ψ :=
    StructuredArrow.homMk ((lisseYonedaFibreProduct.pr f y).op.map ψ) sorry
  map_id := sorry
  map_comp := sorry

/-- The functor sending an object of the flat primed 2-fibre product to the
corresponding structured arrow `f'(pr'(q)) ⟶ y`. -/
def flatYonedaFibreProduct.toStructuredArrow (f : X ⟶ Y) [Flat f]
    (y : flatFppfSite Y) :
    (flatYonedaFibreProduct f y)ᵒᵖ ⥤
      StructuredArrow (op y) (flatFppfMap f).op where
  obj q := StructuredArrow.mk (op (flatYonedaFibreProduct.arrow f y q.unop))
  map {q q'} ψ :=
    StructuredArrow.homMk ((flatYonedaFibreProduct.pr f y).op.map ψ) sorry
  map_id := sorry
  map_comp := sorry

/-- Reindexing the pulled-back sheaf along `toStructuredArrow` does not change
the existence of its limit. -/
instance lisseYonedaFibreProduct.hasLimit_toStructuredArrow_comp
    (f : X ⟶ Y) [Smooth f] (y : lisseEtaleSite Y)
    (H : Sheaf (lisseEtaleTopology X) (Type (u + 1)))
    [HasLimit ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj)] :
    HasLimit
      (lisseYonedaFibreProduct.toStructuredArrow f y ⋙
        StructuredArrow.proj (op y) (lisseEtaleMap f).op ⋙ H.obj) :=
  hasLimit_of_iso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry :
      ((lisseYonedaFibreProduct.pr f y).op ⋙ H.obj) ≅
        lisseYonedaFibreProduct.toStructuredArrow f y ⋙
          StructuredArrow.proj (op y) (lisseEtaleMap f).op ⋙ H.obj)

/-- Reindexing the pulled-back sheaf along the flat `toStructuredArrow` does not
change the existence of its limit. -/
instance flatYonedaFibreProduct.hasLimit_toStructuredArrow_comp
    (f : X ⟶ Y) [Flat f] (y : flatFppfSite Y)
    (H : Sheaf (flatFppfTopology X) (Type (u + 1)))
    [HasLimit ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj)] :
    HasLimit
      (flatYonedaFibreProduct.toStructuredArrow f y ⋙
        StructuredArrow.proj (op y) (flatFppfMap f).op ⋙ H.obj) :=
  hasLimit_of_iso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry :
      ((flatYonedaFibreProduct.pr f y).op ⋙ H.obj) ≅
        flatYonedaFibreProduct.toStructuredArrow f y ⋙
          StructuredArrow.proj (op y) (flatFppfMap f).op ⋙ H.obj)

end AlgebraicGeometry.AlgebraicStack
