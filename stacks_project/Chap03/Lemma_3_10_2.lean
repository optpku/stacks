module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Action.SmallBoundClosed

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

variable {G : Type u} [Group G]

/- Lemma 3.10.2. The small full category of `G`-sets supplied by the preceding lemma
contains the left-regular action, has countable products and coproducts and all fibre
products and pushouts agreeing with the ambient category, and contains every stable
subset of a member up to isomorphism. The full preceding hypothesis is retained as
`Action.IsSmallBoundClosed P`. -/
@[stacks 000V] #check (Action.IsSmallBoundClosed.contains_leftRegular :
  ∀ {P : ObjectProperty (Action (Type u) G)}, Action.IsSmallBoundClosed P →
    P (Action.leftRegular G))

/- Discrete countable diagrams give products and coproducts, including finite and empty
families. Walking cospans give fibre products, and walking spans give pushouts.
The canonical comparison morphisms express agreement with the ambient constructions. -/
#check (Action.hasLimit :
  ∀ {P : ObjectProperty (Action (Type u) G)}, Action.IsSmallBoundClosed P →
    ∀ {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory),
      HasLimit F)
#check (Action.isIso_limit_post :
  ∀ {P : ObjectProperty (Action (Type u) G)}, Action.IsSmallBoundClosed P →
    ∀ {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory)
      [HasLimit F] [HasLimit (F ⋙ P.ι)], IsIso (limit.post F P.ι))
#check (Action.hasColimit :
  ∀ {P : ObjectProperty (Action (Type u) G)}, Action.IsSmallBoundClosed P →
    ∀ {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory),
      HasColimit F)
#check (Action.isIso_colimit_post :
  ∀ {P : ObjectProperty (Action (Type u) G)}, Action.IsSmallBoundClosed P →
    ∀ {J : Type} [SmallCategory J] [CountableCategory J] (F : J ⥤ P.FullSubcategory)
      [HasColimit F] [HasColimit (F ⋙ P.ι)], IsIso (colimit.post F P.ι))

#check (Action.isoClosure_of_stableSubset :
  ∀ {P : ObjectProperty (Action (Type u) G)}, Action.IsSmallBoundClosed P →
    ∀ {U : Action (Type u) G}, P U → ∀ (O : Set U.V)
      (hO : ∀ g : G, Set.MapsTo (fun x : U.V ↦ U.ρ g x) O O),
      P.isoClosure (Action.ofStableSubset U O hO))
