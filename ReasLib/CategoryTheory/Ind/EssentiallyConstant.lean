/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Diagram

/-!
# Hom formulas and essential constancy for ind-objects

This file adds two bridges around mathlib's canonical `Ind`, `Ind.yoneda`, and `Ind.lim` owners:
the limit-colimit formula for morphisms between presented ind-objects, and the equivalence between
presentation-level essential constancy and being isomorphic to a constant ind-object.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.Functor
open scoped CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- No single mathlib declaration states the Hom formula directly for `Ind.lim` objects.
The verified combination of `Ind.inclusion.fullyFaithful.homEquiv`, `Ind.limCompInclusion`, and
`colimitYonedaHomEquiv` gives precisely its owner-level form: evaluating
`colimit (N ⋙ yoneda)` at `op (M.obj i)` is `colim_j Hom_C(M_i, N_j)`. The separate
`RepresentableBy.equivUliftYonedaIso` bridge below records the fixed constant object criterion;
the final theorem then states the presentation-independent criterion directly, without
making representability a replacement definition. -/

namespace Ind

/-- Morphisms from the ind-object of `M` to the ind-object of
`N` are the limit over `i` of the presheaf whose value at `M.obj i` is the colimit over `j` of
`M.obj i ⟶ N.obj j`. -/
@[stacks 05PW "the limit-colimit formula for morphisms of ind-objects"]
noncomputable def limHomEquiv
    {I J : Type v} [SmallCategory I] [IsFiltered I] [SmallCategory J] [IsFiltered J]
    (M : I ⥤ C) (N : J ⥤ C) :
    ((Ind.lim I).obj M ⟶ (Ind.lim J).obj N) ≃
      limit (M.op ⋙ colimit (N ⋙ yoneda)) :=
  Ind.inclusion.fullyFaithful.homEquiv.trans <|
    (Iso.homCongr (Ind.limCompInclusion.app M) (Ind.limCompInclusion.app N)).trans <|
      colimitYonedaHomEquiv M (colimit (N ⋙ yoneda))

/-- The canonical map between the colimit-of-Yoneda realizations of two presented ind-objects
induced by a morphism of their ind-limits. -/
noncomputable def limInclusionMap
    {I J : Type v} [SmallCategory I] [IsFiltered I] [SmallCategory J] [IsFiltered J]
    {M : I ⥤ C} {N : J ⥤ C}
    (f : (Ind.lim I).obj M ⟶ (Ind.lim J).obj N) :
    colimit (M ⋙ yoneda) ⟶ colimit (N ⋙ yoneda) :=
  (Ind.limCompInclusion.app M).inv ≫
    Ind.inclusion.fullyFaithful.homEquiv f ≫
      (Ind.limCompInclusion.app N).hom

/-- `Ind.limHomEquiv` computes a presented ind-morphism by applying the Yoneda Hom-colimit
formula to its canonical realization map. -/
theorem limHomEquiv_apply
    {I J : Type v} [SmallCategory I] [IsFiltered I] [SmallCategory J] [IsFiltered J]
    (M : I ⥤ C) (N : J ⥤ C)
    (f : (Ind.lim I).obj M ⟶ (Ind.lim J).obj N) :
    limHomEquiv M N f =
      colimitYonedaHomEquiv M (colimit (N ⋙ yoneda)) (limInclusionMap f) := sorry

/-- The realization map of the identity of a presented ind-object is the identity. -/
@[simp]
theorem limInclusionMap_id
    {I : Type v} [SmallCategory I] [IsFiltered I] (M : I ⥤ C) :
    limInclusionMap (𝟙 ((Ind.lim I).obj M)) = 𝟙 (colimit (M ⋙ yoneda)) := sorry

/-- Canonical realization maps of presented ind-morphisms preserve composition. -/
@[reassoc]
theorem limInclusionMap_comp
    {I J K : Type v} [SmallCategory I] [IsFiltered I] [SmallCategory J] [IsFiltered J]
    [SmallCategory K] [IsFiltered K]
    {M : I ⥤ C} {N : J ⥤ C} {P : K ⥤ C}
    (f : (Ind.lim I).obj M ⟶ (Ind.lim J).obj N)
    (g : (Ind.lim J).obj N ⟶ (Ind.lim K).obj P) :
    limInclusionMap (f ≫ g) = limInclusionMap f ≫ limInclusionMap g := sorry

/-- The `i`-component of the ind Hom limit-colimit formula evaluates the canonical realization
map on the identity of `M.obj i.unop`. -/
@[simp]
theorem limHomEquiv_π_apply
    {I J : Type v} [SmallCategory I] [IsFiltered I] [SmallCategory J] [IsFiltered J]
    (M : I ⥤ C) (N : J ⥤ C)
    (f : (Ind.lim I).obj M ⟶ (Ind.lim J).obj N) (i : Iᵒᵖ) :
    limit.π (M.op ⋙ colimit (N ⋙ yoneda)) i (limHomEquiv M N f) =
      (limInclusionMap f).app (Opposite.op (M.obj i.unop))
        ((colimit.ι (M ⋙ yoneda) i.unop).app _ (𝟙 (M.obj i.unop))) := sorry

/-- The inclusion of a presented ind-object is canonically its colimit of ulifted Yoneda
presheaves. -/
noncomputable def limInclusionIso
    {I : Type v} [SmallCategory I] [IsFiltered I] (M : I ⥤ C) :
    (Ind.inclusion C).obj ((Ind.lim I).obj M) ≅
      colimit (M ⋙ uliftYoneda.{v}) :=
  Ind.limCompInclusion.app M ≪≫
    (HasColimit.isoOfNatIso (isoWhiskerLeft M uliftYonedaIsoYoneda)).symm

/-- The forward map of `limInclusionIso` is the standard `Ind.limCompInclusion` comparison
followed by transport from Yoneda to ulifted Yoneda. -/
@[simp]
theorem limInclusionIso_hom
    {I : Type v} [SmallCategory I] [IsFiltered I] (M : I ⥤ C) :
    (limInclusionIso M).hom =
      (Ind.limCompInclusion.app M).hom ≫
        (HasColimit.isoOfNatIso
          (isoWhiskerLeft M uliftYonedaIsoYoneda)).inv := sorry

/-- The inverse map of `limInclusionIso` first transports to the ordinary Yoneda colimit and
then uses the inverse `Ind.limCompInclusion` comparison. -/
@[simp]
theorem limInclusionIso_inv
    {I : Type v} [SmallCategory I] [IsFiltered I] (M : I ⥤ C) :
    (limInclusionIso M).inv =
      (HasColimit.isoOfNatIso
        (isoWhiskerLeft M uliftYonedaIsoYoneda)).hom ≫
        (Ind.limCompInclusion.app M).inv := sorry

/-- The inclusion of a constant ind-object is canonically the corresponding ulifted Yoneda
presheaf. -/
noncomputable def yonedaInclusionIso (X : C) :
    (Ind.inclusion C).obj (Ind.yoneda.obj X) ≅ uliftYoneda.obj X :=
  Ind.yonedaCompInclusion.app X ≪≫ (uliftYonedaIsoYoneda.app X).symm

/-- The forward map of `yonedaInclusionIso` is the standard constant-object comparison followed
by the inverse Yoneda-to-ulifted-Yoneda component. -/
@[simp]
theorem yonedaInclusionIso_hom (X : C) :
    (yonedaInclusionIso X).hom =
      (Ind.yonedaCompInclusion.app X).hom ≫
        (uliftYonedaIsoYoneda.app X).inv := sorry

/-- The inverse map of `yonedaInclusionIso` reverses the two canonical comparison maps. -/
@[simp]
theorem yonedaInclusionIso_inv (X : C) :
    (yonedaInclusionIso X).inv =
      (uliftYonedaIsoYoneda.app X).hom ≫
        (Ind.yonedaCompInclusion.app X).inv := sorry

/-- The constant ind-object on `X` is isomorphic to the ind-object of a filtered diagram exactly
when the associated presheaf colimit is represented by `X`. -/
noncomputable def yonedaIsoLimEquivRepresentableBy
    {I : Type v} [SmallCategory I] [IsFiltered I] (M : I ⥤ C) (X : C) :
    (Ind.yoneda.obj X ≅ (Ind.lim I).obj M) ≃
      (colimit (M ⋙ uliftYoneda.{v})).RepresentableBy X :=
  calc
    (Ind.yoneda.obj X ≅ (Ind.lim I).obj M) ≃
        ((Ind.inclusion C).obj (Ind.yoneda.obj X) ≅
          (Ind.inclusion C).obj ((Ind.lim I).obj M)) :=
      Ind.inclusion.fullyFaithful.isoEquiv
    _ ≃ (uliftYoneda.obj X ≅ colimit (M ⋙ uliftYoneda.{v})) :=
      Iso.isoCongr (yonedaInclusionIso X) (limInclusionIso M)
    _ ≃ (colimit (M ⋙ uliftYoneda.{v})).RepresentableBy X :=
      (RepresentableBy.equivUliftYonedaIso _ _).symm

end Ind

namespace IsFiltered

/-- A filtered diagram is essentially constant exactly when its
ind-object is isomorphic to a constant ind-object. -/
@[stacks 05PW "essentially constant diagrams as constant ind-objects"]
theorem isEssentiallyConstant.iff_exists_yonedaIsoLim
    {I : Type v} [SmallCategory I] [IsFiltered I] (M : I ⥤ C) :
    IsEssentiallyConstant M ↔
      ∃ X : C, Nonempty (Ind.yoneda.obj X ≅ (Ind.lim I).obj M) := sorry
/- Proof strategy: in the forward direction, choose an essentially constant cocone. Its splitting
and eventual-factorization data identify the filtered colimit of `M ⋙ uliftYoneda` with the
representable presheaf at the cocone point; transport that representation through
`Ind.yonedaIsoLimEquivRepresentableBy`. Conversely, an isomorphism from a constant ind-object gives
a representation of this presheaf colimit. Represent the universal element at a finite stage of
the filtered colimit; filteredness also realizes the two inverse identities at later common stages,
which supplies exactly the splitting and eventual-factorization fields of
`Cocone.IsEssentiallyConstant`. -/

end IsFiltered

end CategoryTheory
