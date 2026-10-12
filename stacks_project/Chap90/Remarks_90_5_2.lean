/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap90.Remarks_90_5_2_Groupoids
public import stacks_project.Chap90.Remarks_90_5_2_Grothendieck
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass
public import stacks_project.Chap90.Remarks_90_5_2_Pushforward
public import stacks_project.Chap90.Remarks_90_5_2_Restriction
import StacksCheckRecall

@[expose] public section

universe u v w vS vB uF vF

namespace CategoryTheory

open Opposite
open Functor
open scoped Bicategory BasedFunctor TwoFibreProduct

variable {C : Type u} [Category.{v} C]
variable {F : Type uF} [Category.{vF} F]
variable (p : F ⥤ C)

/- Remarks 90.5.2 (1): the fibre category over an object `U` of `C` is `p.Fiber U`; its objects
are those of `F` lying over `U` and its morphisms are those of `F` lying over `𝟙 U`. -/
@[stacks 06GK]
#check (Functor.Fiber p : C → Type uF)

/- Remarks 90.5.2 (2): the fibre categories of a category cofibered in groupoids are groupoids,
so we write `Aut x` for the automorphisms of `x` in a fibre. -/
@[stacks 06GK]
#check (Functor.IsFibered.InGroupoids.fiberIsGroupoid_of_cofibered :
  {F : Type uF} → [Category.{vF} F] → (q : F ⥤ C) → [IsFibered.InGroupoids q.op] →
    (U : C) → IsGroupoid (q.Fiber U))

@[stacks 06GK]
#check (fun (U : C) (x : p.Fiber U) ↦ Aut x : (U : C) → p.Fiber U → Type vF)

/- Remarks 90.5.2 (3): a pushforward of `x` along `f` is a morphism of `F` lying over `f`, and
any two such lifts differ by a unique vertical isomorphism. -/
@[stacks 06GK]
#check (Functor.pushforward_unique :
  {F : Type uF} → [Category.{vF} F] → {q : F ⥤ C} → [IsFibered.InGroupoids q.op] →
    {U V : C} → {x y y' : F} → (f : U ⟶ V) →
      (φ : x ⟶ y) → (ψ : x ⟶ y') → [q.IsHomLift f φ] → [q.IsHomLift f ψ] →
        ∃! τ : y ⟶ y', q.IsHomLift (𝟙 V) τ ∧ φ ≫ τ = ψ ∧ IsIso τ)

/- Remarks 90.5.2 (4): a choice of pushforwards for `p` is a cleavage of `p.op`; such a choice
exists, and each chosen lift is strongly cocartesian. -/
@[stacks 06GK]
#check (Functor.cleavageOp : (q : F ⥤ C) → [IsFibered.InGroupoids q.op] → q.op.Cleavage)

/- Remarks 90.5.2 (5): a morphism of categories cofibered in groupoids over `C` is a functor
commuting with the projections to `C`, i.e. a `1`-morphism of `CofiberedCategoryOver.Groupoids C`. -/
@[stacks 06GK]
#check (fun (X Y : CofiberedCategoryOver.Groupoids.{u, v, w, vS} C) ↦ (X ⟶ Y) :
  CofiberedCategoryOver.Groupoids.{u, v, w, vS} C →
    CofiberedCategoryOver.Groupoids.{u, v, w, vS} C → Type max w vS)

/- Remarks 90.5.2 (6): categories cofibered in groupoids form the `(2,1)`-category
`CofiberedCategoryOver.Groupoids C`, whose `2`-morphisms are vertical based natural
transformations. -/
@[stacks 06GK]
#check (CofiberedCategoryOver.Groupoids.{u, v, w, vS} C :
  Type max (w + 1) (vS + 1) u v)

/- Remarks 90.5.2 (7): a functor `C ⥤ Grpd` determines a category cofibered in groupoids whose
objects are pairs `(U, x)` and whose morphisms are pairs `(f, a)`. -/
@[stacks 06GK]
#check (Functor.ofGroupoidValued :
  (C ⥤ Grpd.{vS, w}) → CofiberedCategoryOver.Groupoids C)

/- Remarks 90.5.2 (8): the functor of fibrewise isomorphism classes of a category cofibered in
groupoids. -/
@[stacks 06GK]
#check (Functor.fiberIsoClassFunctor :
  (q : F ⥤ C) → [IsFibered.InGroupoids q.op] → (C ⥤ Type uF))

/- Remarks 90.5.2 (9): viewing a set as a discrete groupoid, the category-of-elements construction
gives a fully faithful embedding of `C ⥤ Type` into categories cofibered in groupoids over `C`. -/
@[stacks 06GK]
#check (Functor.ofTypeValued : (C ⥤ Type w) → CofiberedCategoryOver.Groupoids C)

@[stacks 06GK]
#check (Functor.ofTypeValuedMap.bijective :
  {F G : C ⥤ Type w} →
    Function.Bijective
      (Functor.ofTypeValuedMap : (F ⟶ G) →
        (Functor.ofTypeValued F ⟶ Functor.ofTypeValued G)))

/- Remarks 90.5.2 (10): the functor `underline U` is `coyoneda.obj (op U)`, and this embedding of
`Cᵒᵖ` into `C ⥤ Type` is fully faithful. -/
@[stacks 06GK]
#check (fun (U : C) ↦ coyoneda.obj (op U) : C → (C ⥤ Type v))

@[stacks 06GK]
#check (Coyoneda.fullyFaithful : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v).FullyFaithful)

/- Remarks 90.5.2 (11): a `2`-fibre product of morphisms of categories cofibered in groupoids is
given by the based pseudo-pullback apex. -/
@[stacks 06GK]
#check (TwoFibreProduct.apex :
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)} →
    [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P] →
      {X Y S : P.FullSubbicategory} →
        (X ⟶ S) → (Y ⟶ S) → P.FullSubbicategory)

/- Remarks 90.5.2 (12): the product of categories cofibered in groupoids is their `2`-fibre
product over the identity cofibered category. -/
@[stacks 06GK]
#check (CofiberedCategoryOver.Groupoids.product :
  (X Y : CofiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C) →
    CofiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C)

/- Remarks 90.5.2 (13): restriction of a category cofibered in groupoids along a full subcategory
of the base remains cofibered in groupoids. -/
@[stacks 06GK]
#check (Functor.restrictTo :
  (q : F ⥤ C) → (P : ObjectProperty C) →
    (P.inverseImage q).FullSubcategory ⥤ P.FullSubcategory)

end CategoryTheory
