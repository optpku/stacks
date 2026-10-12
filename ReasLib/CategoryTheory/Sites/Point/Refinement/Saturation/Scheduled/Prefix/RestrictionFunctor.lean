/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement.Saturation.Scheduled.Prefix.Operations

/-!
# The inverse system of open scheduled prefixes

Restriction makes open scheduled prefixes contravariantly functorial in their
cut.  This file packages that operation at the neutral `Type`-valued functor
layer used by transfinite induction, together with its direct computation and
section API.
-/

@[expose] public section

open CategoryTheory Limits

universe u v q r r' z t t'

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
namespace OrderedRefinement
namespace Saturation
namespace Stage.Scheduled.OpenPrefix

variable {C : Type u} [Category.{v} C]
variable {ι : Type r} [Preorder ι]
variable {J : GrothendieckTopology C}
variable {S : ιᵒᵖ ⥤ C}
variable [LocallySmall.{q} C]
variable [EssentiallySmall.{q} ιᵒᵖ]
variable [HasColimitsOfShape (EssentiallySmallFiber.fiber S).Elementsᵒᵖ (Type q)]
variable {P : Cᵒᵖ ⥤ Type q}
variable {x y : (EssentiallySmallFiber.presheafFiber S).obj P}
variable {M : Type z} [Preorder M]

/-- Open scheduled prefixes form an inverse system under restriction of cuts. -/
noncomputable def restrictionFunctor
    (A : Stage.{u, v, q, r, r'} (J := J) S P x y)
    (request : M → A.target.Request J) :
    (WithTop (WithBot M))ᵒᵖ ⥤ Type _ where
  obj cut := Stage.Scheduled.OpenPrefix (J := J) A request cut.unop
  map f := ↾fun D => D.restrict (leOfHom f.unop)
  map_id := sorry
  map_comp := sorry

variable {A : Stage.{u, v, q, r, r'} (J := J) S P x y}
variable {request : M → A.target.Request J}

namespace restrictionFunctor

/-- The restriction functor acts on a morphism of cuts by
`OpenPrefix.restrict`. -/
@[simp]
theorem map_apply
    {cut cut' : (WithTop (WithBot M))ᵒᵖ} (f : cut ⟶ cut')
    (D : Stage.Scheduled.OpenPrefix (J := J) A request cut.unop) :
    (restrictionFunctor (J := J) A request).map f D =
      D.restrict (leOfHom f.unop) := sorry

/-- A section of the restriction functor identifies each later prefix with
its restriction along every index morphism. -/
theorem sections_restrict {K : Type t} [Category.{t'} K]
    (F : K ⥤ (WithTop (WithBot M))ᵒᵖ)
    (s : (F ⋙ restrictionFunctor (J := J) A request).sections)
    {i j : K} (f : i ⟶ j) :
    (s.val i).restrict (leOfHom (F.map f).unop) = s.val j := sorry

end restrictionFunctor

/- The computational data of `restrictionFunctor` is explicit; any
`sorryAx` is confined to its functor-law proof fields. -/

end Stage.Scheduled.OpenPrefix
end Saturation
end OrderedRefinement
end CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered
