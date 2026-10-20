/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Ind.EssentiallyConstant

/-!
# Pro-objects

`Pro C` is the opposite of `Ind Cᵒᵖ`.  This file owns the constant-system embedding, realization,
cofiltered-diagram presentation, limit-colimit Hom formula, and the invariant characterization of
essentially constant presentations.

The public `Pro.lim` accepts any appropriately small and locally small index category.  The
object-and-Hom smallification required by mathlib's `Ind.lim` stays internal to the construction.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.Functor
open Opposite
open scoped CategoryTheory

universe uC vC uI vI uJ vJ

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]

/-
The pro-category is the free completion under cofiltered limits, equivalently the opposite of
`Ind(Cᵒᵖ)`. Mathlib currently supplies the complete `Ind` side but no `Pro` owner. Repeating
`((Ind Cᵒᵖ)ᵒᵖ)` in every public statement would expose variance and universe implementation details,
so this module gives that major mathematical object its own owner. Unlike a one-field predicate alias,
`Pro` supports a constant embedding, a presentation functor, and all later pro-object APIs.

Mathlib's `Ind.lim` requires its index category to live exactly in the Hom universe of `C`.
That restriction is an implementation detail: for example, it otherwise prevents a sequence
`ℕᵒᵖ ⥤ C` from presenting a pro-object in a general `Category.{vC} C`. The implementation of
`Pro.lim` therefore shrinks both objects and Hom types of any `vC`-small, `vC`-locally-small index
category before applying `Ind.lim`. The smallification stays inside the defining terms, while the
public functor and the limit-colimit Hom formula retain the original diagram and its readable
mathematical shape.
-/

variable (C) in
/-- The category of pro-objects of `C`, modeled as the opposite
of the ind-category of `Cᵒᵖ`. -/
@[stacks 05PX "the category of pro-objects"]
def Pro : Type (max uC (vC + 1)) :=
  (Ind Cᵒᵖ)ᵒᵖ

/-- The canonical `vC`-category structure on `Pro C`. -/
noncomputable instance : Category.{vC} (Pro C) :=
  inferInstanceAs (Category.{vC} ((Ind Cᵒᵖ)ᵒᵖ))

/-- The canonical realization of pro-objects as the opposite of the category of covariant
`Type vC`-valued functors. A morphism of pro-objects therefore induces a natural transformation
from the target realization to the source realization. -/
protected noncomputable def Pro.inclusion (C : Type uC) [Category.{vC} C] :
    Pro C ⥤ (C ⥤ Type vC)ᵒᵖ :=
  (Ind.inclusion Cᵒᵖ).op ⋙
    ((opOpEquivalence C).congrLeft (E := Type vC)).functor.op

/-- The canonical realization `Pro C ⥤ (C ⥤ Type vC)ᵒᵖ` is fully faithful. -/
protected noncomputable def Pro.inclusion.fullyFaithful :
    (Pro.inclusion C).FullyFaithful :=
  Ind.inclusion.fullyFaithful.op.comp
    ((opOpEquivalence C).congrLeft (E := Type vC)).fullyFaithfulFunctor.op

/-- The canonical realization of pro-objects is full. -/
noncomputable instance : (Pro.inclusion C).Full :=
  Pro.inclusion.fullyFaithful.full

/-- The canonical realization of pro-objects is faithful. -/
noncomputable instance : (Pro.inclusion C).Faithful :=
  Pro.inclusion.fullyFaithful.faithful

/-- The canonical functor from `C` to `Pro C` sends an object to
its constant pro-object. -/
@[stacks 05PX "the constant-system embedding"]
protected noncomputable def Pro.yoneda : C ⥤ Pro C :=
  (opOpEquivalence C).inverse ⋙ Ind.yoneda.op

/-- The constant-system embedding `Pro.yoneda : C ⥤ Pro C` is
fully faithful. -/
@[stacks 05PX "full faithfulness of the constant-system embedding"]
protected noncomputable def Pro.yoneda.fullyFaithful :
    (Pro.yoneda (C := C)).FullyFaithful :=
  (opOpEquivalence C).fullyFaithfulInverse.comp Ind.yoneda.fullyFaithful.op

/-- The constant-system embedding into `Pro C` is full. -/
noncomputable instance : (Pro.yoneda (C := C)).Full :=
  Pro.yoneda.fullyFaithful.full

/-- The constant-system embedding into `Pro C` is faithful. -/
noncomputable instance : (Pro.yoneda (C := C)).Faithful :=
  Pro.yoneda.fullyFaithful.faithful

/-- A small cofiltered diagram determines its canonical
pro-object through `Pro.lim`. The index category may live in any universe, provided its objects
and Hom types are `vC`-small. -/
@[stacks 05PX "cofiltered diagrams as pro-objects"]
protected noncomputable def Pro.lim
    (I : Type uI) [Category.{vI} I] [Small.{vC} I] [LocallySmall.{vC} I]
    [IsCofiltered I] : (I ⥤ C) ⥤ Pro C :=
  let e : I ≌ ShrinkHoms.{vC} (Shrink.{vC} I) :=
    (Shrink.equivalence.{vC} I).trans
      (ShrinkHoms.equivalence.{vC} (Shrink.{vC} I))
  -- Local instance justification (defeq pin): `Ind.lim` consumes the smallified index only.
  letI : IsCofiltered (ShrinkHoms.{vC} (Shrink.{vC} I)) :=
    IsCofiltered.of_equivalence e
  e.congrLeft.functor ⋙
    (whiskeringRight _ _ _).obj (opOpEquivalence C).inverse ⋙
      (leftOpRightOpEquiv (ShrinkHoms.{vC} (Shrink.{vC} I)) (Cᵒᵖ)).inverse ⋙
        (Ind.lim (ShrinkHoms.{vC} (Shrink.{vC} I))ᵒᵖ).op

namespace Pro

/-- Morphisms from the pro-object of `F` to the pro-object of
`G` are `lim_j colim_i (F.obj i ⟶ G.obj j)`. -/
@[stacks 05PX "the limit-colimit formula for morphisms of pro-objects"]
noncomputable def limHomEquiv
    {I : Type uI} [Category.{vI} I] [Small.{vC} I] [LocallySmall.{vC} I]
    [IsCofiltered I] {J : Type uJ} [Category.{vJ} J] [Small.{vC} J]
    [LocallySmall.{vC} J] [IsCofiltered J] (F : I ⥤ C) (G : J ⥤ C) :
    ((Pro.lim I).obj F ⟶ (Pro.lim J).obj G) ≃
      limit (G.op.op ⋙ colimit (F.op ⋙ yoneda)) :=
  let eI : I ≌ ShrinkHoms.{vC} (Shrink.{vC} I) :=
    (Shrink.equivalence.{vC} I).trans
      (ShrinkHoms.equivalence.{vC} (Shrink.{vC} I))
  let eJ : J ≌ ShrinkHoms.{vC} (Shrink.{vC} J) :=
    (Shrink.equivalence.{vC} J).trans
      (ShrinkHoms.equivalence.{vC} (Shrink.{vC} J))
  -- Local instance justification (defeq pin): this invokes `Ind.lim` on the smallified source.
  letI : IsCofiltered (ShrinkHoms.{vC} (Shrink.{vC} I)) :=
    IsCofiltered.of_equivalence eI
  -- Local instance justification (defeq pin): this invokes `Ind.lim` on the smallified target.
  letI : IsCofiltered (ShrinkHoms.{vC} (Shrink.{vC} J)) :=
    IsCofiltered.of_equivalence eJ
  let qF : colimit ((eI.inverse ⋙ F).op ⋙ yoneda) ≅ colimit (F.op ⋙ yoneda) :=
    (HasColimit.isoOfEquivalence eI.op
      (eI.op.funInvIdAssoc (F.op ⋙ yoneda))).symm
  let q : limit ((eJ.inverse ⋙ G).op.op ⋙
      colimit ((eI.inverse ⋙ F).op ⋙ yoneda)) ≅
        limit (G.op.op ⋙ colimit (F.op ⋙ yoneda)) :=
    (HasLimit.isoOfEquivalence eJ.op.op
      ((eJ.op.op.funInvIdAssoc
        (G.op.op ⋙ colimit ((eI.inverse ⋙ F).op ⋙ yoneda))) ≪≫
          isoWhiskerLeft G.op.op qF)).symm
  ((opEquiv _ _).trans
    (Ind.limHomEquiv ((eJ.inverse ⋙ G).op) ((eI.inverse ⋙ F).op))).trans q.toEquiv

end Pro

namespace IsCofiltered

/-- A cofiltered diagram is essentially constant exactly when
its pro-object is isomorphic to a constant pro-object. -/
@[stacks 05PX "essentially constant diagrams as constant pro-objects"]
theorem isEssentiallyConstant.iff_exists_limIsoYoneda
    {I : Type uI} [Category.{vI} I] [Small.{vC} I] [LocallySmall.{vC} I]
    [IsCofiltered I] (F : I ⥤ C) :
    IsEssentiallyConstant F ↔
      ∃ X : C, Nonempty ((Pro.lim I).obj F ≅ Pro.yoneda.obj X) := sorry
/- Proof strategy: reindex `F` along the object-and-Hom smallification equivalence used in
`Pro.lim`, and use invariance of essential constancy under equivalence of index categories. Apply
`IsFiltered.isEssentiallyConstant.iff_exists_yonedaIsoLim` to the opposite of the smallified
diagram, take opposites of the resulting isomorphisms, and transport back through the definition of
`Pro.lim`. -/

end IsCofiltered

end CategoryTheory
