module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Whiskering
public import stacks_project.Chap90.Definition_90_21_1_Groupoid

/-!
# Restriction of groupoids in functors

Restriction of a groupoid in functors along a functor `ι : C' ⥤ C` (in particular, along
a subcategory inclusion) is precomposition on object/arrow functors and left whiskering on
structure maps, with composition transported by the pullback-preservation isomorphism.
-/

@[expose] public section

open CategoryTheory Functor Limits

noncomputable section

universe u u' u'' v v' v'' w

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C] [HasPullbacks (C ⥤ Type w)]

/-- Restriction of a groupoid in functors along `ι : C' ⥤ C`. When `C'` is a subcategory of
`C`, take `ι` to be `ObjectProperty.ι` or `wideSubcategoryInclusion W ⋙ P.ι`. -/
def restrict {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    GroupoidInFunctors.{u', v', w} C' where
  U := ι ⋙ G.U
  R := ι ⋙ G.R
  s := whiskerLeft ι G.s
  t := whiskerLeft ι G.t
  c := (PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
      whiskerLeft ι G.c
  e := whiskerLeft ι G.e
  i := whiskerLeft ι G.i
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- Restriction of the object functor is precomposition with `ι`. -/
theorem restrict_U {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).U = ι ⋙ G.U := sorry

/-- Restriction of the arrow functor is precomposition with `ι`. -/
theorem restrict_R {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).R = ι ⋙ G.R := sorry

/-- Restriction of the source transformation is left whiskering by `ι`. -/
theorem restrict_s {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).s = whiskerLeft ι G.s := sorry

/-- Restriction of the target transformation is left whiskering by `ι`. -/
theorem restrict_t {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).t = whiskerLeft ι G.t := sorry

/-- Restriction of composition is left whiskering, transported by the pullback-preservation
isomorphism of `(whiskeringLeft C' C (Type w)).obj ι`. -/
theorem restrict_c {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).c =
      (PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
        whiskerLeft ι G.c := sorry

/-- Restriction of the identity-arrow map is left whiskering by `ι`. -/
theorem restrict_e {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).e = whiskerLeft ι G.e := sorry

/-- Restriction of the inverse-arrow map is left whiskering by `ι`. -/
theorem restrict_i {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).i = whiskerLeft ι G.i := sorry

/-- The restricted groupoid in functors is the source quintuple `(U, R, s, t, c)` together
with the identity and inverse maps, with functors precomposed by `ι` and structure maps
left-whiskered by `ι`. -/
theorem restrict_spec {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) :
    (G.restrict ι).U = ι ⋙ G.U ∧
      (G.restrict ι).R = ι ⋙ G.R ∧
      (G.restrict ι).s = whiskerLeft ι G.s ∧
      (G.restrict ι).t = whiskerLeft ι G.t ∧
      (G.restrict ι).c =
        (PreservesPullback.iso ((whiskeringLeft C' C (Type w)).obj ι) G.s G.t).inv ≫
          whiskerLeft ι G.c ∧
      (G.restrict ι).e = whiskerLeft ι G.e ∧
      (G.restrict ι).i = whiskerLeft ι G.i := sorry

/-- Restriction along the identity functor recovers the original groupoid in functors. -/
theorem restrict_id (G : GroupoidInFunctors.{u, v, w} C) : G.restrict (𝟭 C) = G := sorry

/-- Restriction along a composite inclusion is the composite of restrictions. -/
theorem restrict_comp {C' : Type u'} [Category.{v'} C'] [HasPullbacks (C' ⥤ Type w)]
    {C'' : Type u''} [Category.{v''} C''] [HasPullbacks (C'' ⥤ Type w)]
    (G : GroupoidInFunctors.{u, v, w} C) (ι : C' ⥤ C) (ι' : C'' ⥤ C') :
    G.restrict (ι' ⋙ ι) = (G.restrict ι).restrict ι' := sorry

end CategoryTheory.GroupoidInFunctors
