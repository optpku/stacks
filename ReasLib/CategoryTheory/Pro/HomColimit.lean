/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.IndYoneda
public import ReasLib.CategoryTheory.Pro.Presentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hom-colimit realization of presented pro-objects

A cofiltered presentation `F` determines the covariant Hom-colimit functor
`X ↦ colim_i (F.obj i ⟶ X)`.  The canonical realization of its pro-object is naturally isomorphic
to this functor, so pro-morphisms become natural transformations and then compatible
limit-colimit families.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.Functor
open Opposite
open scoped CategoryTheory

universe uC vC uI vI uJ vJ uK vK

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]

/-
Mathlib's `Limits.colimitCoyonedaHomIsoLimit'` already says that transformations out of
`colimit (G.op ⋙ coyoneda)` are compatible families obtained by evaluation on identity classes;
its theorem `Limits.colimitCoyonedaHomIsoLimit'_π_apply` gives the corresponding component formula
without rebuilding the correspondence through local declarations and universe lifts.

The primary surface below uses the canonical `Pro` owner. Both the pro-object and its realization
accept an index category in an arbitrary universe, provided its objects and Hom types are
`vC`-small. The smallification needed by mathlib's `Ind.lim` remains internal to
`limInclusionIso`; its final factor transports the computed colimit back along the index
equivalence, so the public realization is still the readable source expression
`colimit (F.op ⋙ coyoneda)`.
-/

namespace Pro

/-- The covariant functor represented by a pro-system presentation `F`, sending `X` to
`colim_i (F.obj i ⟶ X)`. -/
noncomputable def homColimit
    {I : Type uI} [Category.{vI} I] [Small.{vC} I] (F : I ⥤ C) : C ⥤ Type vC :=
  colimit (F.op ⋙ coyoneda)

/-- The canonical realization of the pro-object presented by `F` is its Hom-colimit functor. -/
noncomputable def limInclusionIso
    {I : Type uI} [Category.{vI} I] [Small.{vC} I] [LocallySmall.{vC} I]
    [IsCofiltered I] (F : I ⥤ C) :
    ((Pro.inclusion C).obj ((Pro.lim I).obj F)).unop ≅ homColimit F :=
  let e : I ≌ ShrinkHoms.{vC} (Shrink.{vC} I) :=
    (Shrink.equivalence.{vC} I).trans
      (ShrinkHoms.equivalence.{vC} (Shrink.{vC} I))
  -- Local instance justification (defeq pin): `Ind.limCompInclusion` uses the smallified index.
  letI : IsCofiltered (ShrinkHoms.{vC} (Shrink.{vC} I)) :=
    IsCofiltered.of_equivalence e
  let F' : ShrinkHoms.{vC} (Shrink.{vC} I) ⥤ C := e.inverse ⋙ F
  let K := (whiskeringLeft C Cᵒᵖᵒᵖ (Type vC)).obj (opOp C)
  let q : homColimit F' ≅ homColimit F :=
    (HasColimit.isoOfEquivalence e.op
      (e.op.funInvIdAssoc (F.op ⋙ coyoneda))).symm
  (isoWhiskerLeft (opOp C) (Ind.limCompInclusion.app F'.op)) ≪≫
    preservesColimitIso K (F'.op ⋙ yoneda) ≪≫
      HasColimit.isoOfNatIso
        (Functor.associator F'.op yoneda K ≪≫ isoWhiskerLeft F'.op Coyoneda.opIso) ≪≫ q

/-- A morphism between the pro-objects presented by `F` and `G` is equivalently a natural
transformation from the Hom-colimit functor of `G` to that of `F`. -/
@[stacks 0G2X "pro-object morphisms as transformations of Hom-colimit functors"]
noncomputable def homColimit.homEquiv
    {I : Type uI} [Category.{vI} I] [Small.{vC} I] [LocallySmall.{vC} I]
    [IsCofiltered I] {J : Type uJ} [Category.{vJ} J] [Small.{vC} J]
    [LocallySmall.{vC} J] [IsCofiltered J] (F : I ⥤ C) (G : J ⥤ C) :
    ((Pro.lim I).obj F ⟶ (Pro.lim J).obj G) ≃
      (homColimit G ⟶ homColimit F) :=
  Pro.inclusion.fullyFaithful.homEquiv.trans <|
    (opEquiv _ _).trans <|
      Iso.homCongr (limInclusionIso G) (limInclusionIso F)

namespace homColimit

/-- The contravariant action on Hom-colimit functors induced by a morphism of presented
pro-objects. -/
noncomputable def map
    {I : Type uI} [Category.{vI} I] [Small.{vC} I] [LocallySmall.{vC} I]
    [IsCofiltered I] {J : Type uJ} [Category.{vJ} J] [Small.{vC} J]
    [LocallySmall.{vC} J] [IsCofiltered J] {F : I ⥤ C} {G : J ⥤ C}
    (f : (Pro.lim I).obj F ⟶ (Pro.lim J).obj G) :
    Pro.homColimit G ⟶ Pro.homColimit F :=
  Pro.homColimit.homEquiv F G f

/-- The identity morphism of a presented pro-object induces the identity transformation of
its Hom-colimit functor. -/
@[simp]
theorem map_id
    {I : Type uI} [Category.{vI} I] [Small.{vC} I] [LocallySmall.{vC} I]
    [IsCofiltered I] (F : I ⥤ C) :
    map (𝟙 ((Pro.lim I).obj F)) = 𝟙 (Pro.homColimit F) := sorry

/-- Composition of presented pro-object morphisms acts contravariantly on their
Hom-colimit functors. -/
@[reassoc]
theorem map_comp
    {I : Type uI} [Category.{vI} I] [Small.{vC} I] [LocallySmall.{vC} I]
    [IsCofiltered I] {J : Type uJ} [Category.{vJ} J] [Small.{vC} J]
    [LocallySmall.{vC} J] [IsCofiltered J] {K : Type uK} [Category.{vK} K]
    [Small.{vC} K] [LocallySmall.{vC} K] [IsCofiltered K]
    {F : I ⥤ C} {G : J ⥤ C} {H : K ⥤ C}
    (f : (Pro.lim I).obj F ⟶ (Pro.lim J).obj G)
    (g : (Pro.lim J).obj G ⟶ (Pro.lim K).obj H) :
    map (f ≫ g) = map g ≫ map f := sorry

/-- Natural transformations between the Hom-colimit functors of `G` and `F` are equivalently the
compatible families in `lim_j colim_i (F.obj i ⟶ G.obj j)`. -/
@[stacks 0G2X "transformations as compatible Hom-colimit families"]
noncomputable def natTransEquivLimit
    {I : Type uI} [Category.{vI} I] [Small.{vC} I]
    {J : Type uJ} [Category.{vJ} J] [Small.{vC} J]
    (F : I ⥤ C) (G : J ⥤ C) :
    (Pro.homColimit G ⟶ Pro.homColimit F) ≃
      limit (G ⋙ Pro.homColimit F) :=
  -- Local instance justification (instance diamond): the comparison needs `Small.{max uC vC} J`
  -- alongside the caller's `Small.{vC} J`; a global lift would create competing `Small` paths.
  letI : Small.{max uC vC} J := small_lift J
  let e :
      limit (G ⋙ Pro.homColimit F ⋙ uliftFunctor.{uC, vC}) ≃
        limit (G ⋙ Pro.homColimit F) :=
    (preservesLimitIso (uliftFunctor.{uC, vC}) (G ⋙ Pro.homColimit F)).symm.toEquiv.trans
      (Equiv.ulift : ULift (limit (G ⋙ Pro.homColimit F)) ≃
        limit (G ⋙ Pro.homColimit F))
  (Limits.colimitCoyonedaHomIsoLimit' G (Pro.homColimit F)).toEquiv.trans e

/-- The compatible family associated to a transformation is obtained at `j` by evaluating the
transformation on the identity class of `G.obj j`. -/
@[stacks 0G2X "evaluation on identity classes", simp]
theorem natTransEquivLimit_π_apply
    {I : Type uI} [Category.{vI} I] [Small.{vC} I]
    {J : Type uJ} [Category.{vJ} J] [Small.{vC} J]
    (F : I ⥤ C) (G : J ⥤ C)
    (η : Pro.homColimit G ⟶ Pro.homColimit F) (j : J) :
    limit.π (G ⋙ Pro.homColimit F) j (natTransEquivLimit F G η) =
      η.app (G.obj j)
        ((colimit.ι (G.op ⋙ coyoneda) (op j)).app (G.obj j) (𝟙 (G.obj j))) := sorry

end homColimit

end Pro

end CategoryTheory
