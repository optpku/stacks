module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Reindex.MapIso.Basic
public import ReasLib.CategoryTheory.Fibered.Cleavage.Pseudofunctor.Construction

/-!
# Naturality of cartesian-functor reindexing comparisons

This module gives fiber, total-category, pseudofunctor-map, and conjugation forms of the
objectwise reindexing comparison.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

universe uS₁ vS₁ uS₂ vS₂

namespace CartesianBasedFunctor

variable {S₁ : Type uS₁} {S₂ : Type uS₂} [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

/-- The componentwise reindexing comparison is natural in the source fiber object. -/
theorem Reindex.mapIso.hom.naturality
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    (f⁎[χ₂]).map ((F.fiberFunctor U).map α) ≫
        (Reindex.mapIso F χ₁ χ₂ f y).hom =
      (Reindex.mapIso F χ₁ χ₂ f x).hom ≫
        (F.fiberFunctor V).map ((f⁎[χ₁]).map α) := sorry
/- Proof strategy: forget to the total category and postcompose with the target cartesian arrow;
use the two factorization identities and functoriality to reduce both sides to the same map. -/

/-- Naturality of the forward comparison after forgetting fiber morphisms to the target total
category. -/
@[reassoc]
theorem Reindex.mapIso.hom.naturalityTotal
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    ((f⁎[χ₂]).map ((F.fiberFunctor U).map α)).1 ≫
        (Reindex.mapIso F χ₁ χ₂ f y).hom.1 =
      (Reindex.mapIso F χ₁ χ₂ f x).hom.1 ≫
        ((F.fiberFunctor V).map ((f⁎[χ₁]).map α)).1 := sorry
/- Proof strategy: apply `congrArg (fun k ↦ k.1)` to
`Reindex.mapIso.hom.naturality F χ₁ χ₂ f α`. -/

/-- Naturality of the forward reindexing comparison in the map presentation of the canonical
fiber pseudofunctors.

This is the source-facing form for descent and `pullHom` calculations associated with the two
displayed cleavages. -/
theorem Reindex.mapIso.hom.mapNaturality
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    (χ₂.toPseudofunctor.map f.op.toLoc).toFunctor.map
          ((F.fiberFunctor U).map α) ≫
        (Reindex.mapIso F χ₁ χ₂ f y).hom =
      (Reindex.mapIso F χ₁ χ₂ f x).hom ≫
        (F.fiberFunctor V).map
          ((χ₁.toPseudofunctor.map f.op.toLoc).toFunctor.map α) := sorry
/- Proof strategy: transport `Reindex.mapIso.hom.naturality F χ₁ χ₂ f α` across
`toPseudofunctor.mapIso χ₁` and `toPseudofunctor.mapIso χ₂`; both bridges are `eqToIso`, so
equality elimination reduces the statement to the cleavage presentation. -/

/-- Naturality of the inverse reindexing comparison. -/
theorem Reindex.mapIso.inv.naturality
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    (F.fiberFunctor V).map ((f⁎[χ₁]).map α) ≫
        (Reindex.mapIso F χ₁ χ₂ f y).inv =
      (Reindex.mapIso F χ₁ χ₂ f x).inv ≫
        (f⁎[χ₂]).map ((F.fiberFunctor U).map α) := sorry
/- Proof strategy: conjugate `Reindex.mapIso.hom.naturality F χ₁ χ₂ f α` by the inverse
components and cancel the two inverse laws. -/

/-- Total-category readout of inverse reindexing-comparison naturality. This avoids repeated
forgetful coercions in computations performed in the total category. -/
@[reassoc]
theorem Reindex.mapIso.inv.naturalityTotal
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    ((F.fiberFunctor V).map ((f⁎[χ₁]).map α)).1 ≫
        (Reindex.mapIso F χ₁ χ₂ f y).inv.1 =
      (Reindex.mapIso F χ₁ χ₂ f x).inv.1 ≫
        ((f⁎[χ₂]).map ((F.fiberFunctor U).map α)).1 := sorry
/- Proof strategy: apply `congrArg (fun k ↦ k.1)` to
`Reindex.mapIso.inv.naturality F χ₁ χ₂ f α`. -/

/-- Naturality of the inverse reindexing comparison in the map presentation of the canonical
fiber pseudofunctors.

This orientation rewrites a comparison inverse followed by a mapped arrow, which is the useful
form in `pullHom` and conjugation calculations. -/
theorem Reindex.mapIso.inv.mapNaturality
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    (Reindex.mapIso F χ₁ χ₂ f x).inv ≫
        (χ₂.toPseudofunctor.map f.op.toLoc).toFunctor.map
          ((F.fiberFunctor U).map α) =
      (F.fiberFunctor V).map
          ((χ₁.toPseudofunctor.map f.op.toLoc).toFunctor.map α) ≫
        (Reindex.mapIso F χ₁ χ₂ f y).inv := sorry
/- Proof strategy: reverse `Reindex.mapIso.inv.naturality F χ₁ χ₂ f α`, then transport its
source and target reindexing functors across the two `toPseudofunctor.mapIso` bridges. -/

/-- Applying a cartesian based functor to a reindexed fiber morphism is the reindexing of its
image conjugated by the two comparison isomorphisms. -/
theorem Reindex.mapIso.conjugation.fiber
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    (F.fiberFunctor V).map ((f⁎[χ₁]).map α) =
      (Reindex.mapIso F χ₁ χ₂ f x).inv ≫
        (f⁎[χ₂]).map ((F.fiberFunctor U).map α) ≫
        (Reindex.mapIso F χ₁ χ₂ f y).hom := sorry

/-- Reindexing the image of a fiber morphism is obtained by conjugating the image of its
reindexing by the forward comparison isomorphisms. -/
theorem Reindex.mapIso.conjugation.reindex
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    (f⁎[χ₂]).map ((F.fiberFunctor U).map α) =
      (Reindex.mapIso F χ₁ χ₂ f x).hom ≫
        (F.fiberFunctor V).map ((f⁎[χ₁]).map α) ≫
        (Reindex.mapIso F χ₁ χ₂ f y).inv := sorry

/-- Total-category readout of `Reindex.mapIso.conjugation.fiber`. -/
theorem Reindex.mapIso.conjugation.totalFiber
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    ((F.fiberFunctor V).map ((f⁎[χ₁]).map α)).1 =
      (Reindex.mapIso F χ₁ χ₂ f x).inv.1 ≫
        ((f⁎[χ₂]).map ((F.fiberFunctor U).map α)).1 ≫
        (Reindex.mapIso F χ₁ χ₂ f y).hom.1 := sorry

/-- Total-category readout of `Reindex.mapIso.conjugation.reindex`. -/
theorem Reindex.mapIso.conjugation.totalReindex
    (F : CartesianBasedFunctor p₁ p₂) (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {U V : C} (f : V ⟶ U) {x y : p₁.Fiber U} (α : x ⟶ y) :
    ((f⁎[χ₂]).map ((F.fiberFunctor U).map α)).1 =
      (Reindex.mapIso F χ₁ χ₂ f x).hom.1 ≫
        ((F.fiberFunctor V).map ((f⁎[χ₁]).map α)).1 ≫
        (Reindex.mapIso F χ₁ χ₂ f y).inv.1 := sorry

end CartesianBasedFunctor

end CategoryTheory
