/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Reindex.Composition
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Pseudofunctor.Reindex.Identity

/-!
# Coherence for Pointwise Pullback Reindexing

This leaf records the associativity and unit coherence equations for the composition and identity
comparisons of pointwise categorical-pullback reindexing.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback Opposite
open scoped CategoricalPullback CategoryTheory.Bicategory

universe uC vC uD vD uF vF uG vG uH vH

namespace CategoryTheory

namespace Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {u : C ⥤ D}
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vG, uG}}
variable {H : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vH, uH}}

/-- Associativity coherence for pointwise categorical pullbacks of indexed functors. -/
theorem Pullback.Reindex.Coherence.associator
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V W Z : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (h : W ⟶ Z) :
    (Cat.Hom.isoMk
          (Pullback.Reindex.mapCompIso L R (f ≫ g).unop h.unop)).hom ≫
        (Cat.Hom.isoMk (Pullback.Reindex.mapCompIso L R f.unop g.unop)).hom ▷
          (Pullback.Reindex.functor L R h.unop).toCatHom ≫
        (α_ (Pullback.Reindex.functor L R f.unop).toCatHom
          (Pullback.Reindex.functor L R g.unop).toCatHom
          (Pullback.Reindex.functor L R h.unop).toCatHom).hom ≫
        (Pullback.Reindex.functor L R f.unop).toCatHom ◁
          (Cat.Hom.isoMk (Pullback.Reindex.mapCompIso L R g.unop h.unop)).inv ≫
        (Cat.Hom.isoMk
          (Pullback.Reindex.mapCompIso L R f.unop (g ≫ h).unop)).inv =
      eqToHom (congrArg
        (fun k ↦ (Pullback.Reindex.functor L R k.unop).toCatHom)
        (Category.assoc f g h)) := sorry

/-- Left-unit coherence for pointwise categorical pullbacks of indexed functors. -/
theorem Pullback.Reindex.Coherence.leftUnitor
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (Cat.Hom.isoMk
          (Pullback.Reindex.mapCompIso L R (𝟙 U).unop f.unop)).hom ≫
        (Cat.Hom.isoMk (Pullback.Reindex.mapIdIso L R (unop U))).hom ▷
          (Pullback.Reindex.functor L R f.unop).toCatHom ≫
        (λ_ (Pullback.Reindex.functor L R f.unop).toCatHom).hom =
      eqToHom (congrArg
        (fun k ↦ (Pullback.Reindex.functor L R k.unop).toCatHom)
        (Category.id_comp f)) := sorry

/-- Right-unit coherence for pointwise categorical pullbacks of indexed functors. -/
theorem Pullback.Reindex.Coherence.rightUnitor
    (L : IndexedFunctor u F H) (R : IndexedFunctor u G H)
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (Cat.Hom.isoMk
          (Pullback.Reindex.mapCompIso L R f.unop (𝟙 V).unop)).hom ≫
        (Pullback.Reindex.functor L R f.unop).toCatHom ◁
          (Cat.Hom.isoMk (Pullback.Reindex.mapIdIso L R (unop V))).hom ≫
        (ρ_ (Pullback.Reindex.functor L R f.unop).toCatHom).hom =
      eqToHom (congrArg
        (fun k ↦ (Pullback.Reindex.functor L R k.unop).toCatHom)
        (Category.comp_id f)) := sorry

end Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor

end CategoryTheory
